------------------------------------------------------------------------
-- Typed example computations at quotas on the operations.            --
--                                                                    --
-- Effect grades and resource grades are both `⟪ r , w , s ⟫ᵐ`, "at   --
-- most `r` reads, `w` writes and `s` sends", and each operation is   --
-- graded by one draw on its own counter. Idling draws on none:       --
-- `delay` locks the context by the unit.                             --
--                                                                    --
-- As an effect grade, a quota is a rate limit that a computation     --
-- keeps, and `coerce` may raise it. As a resource grade it bounds    --
-- the number of operations performed since boxing, and               --
-- `[ ⟪ r , w , s ⟫ᵐ ] A` is a licence, claimable until the quota is  --
-- spent, irrespective of time.                                       --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
--                                                                    --
--   * the bound `ρ ≾ᵣ uᵣ` of `var` holds when `ρ` counts nothing, so --
--     a reading survives any amount of idling and no operation;      --
--     after an operation it must be licensed.                        --
--                                                                    --
--   * a handler clause may discard its continuation: performing      --
--     nothing keeps every quota.                                     --
--                                                                    --
-- Every claim is checked counter by counter: `≤!` on a quota, `tt`   --
-- on an `unlimited` one. A refutation names the counter that         --
-- overflows.                                                         --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding.                                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Counts.AtMost where

open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Time.RightSided using (uₒ-least)
open import Syntax.Grades.Example.Counts.AtMost
  using (at-most-counts; upto; unlimited; uᵛ-least)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send)
open import Syntax.Grades.Example.Worked.Counts.Index using (Quota; ⟪_,_,_⟫ᵐ)

open import Syntax.Grades.Example.Worked.Time.Decide using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, each drawing once on its own counter

opTime : Op → Quota
opTime read  = ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ
opTime write = ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ
opTime send  = ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ

open import Syntax.Grades.Example.System.Identity using (noWitnesses)
open import Syntax.Grades.Example.Worked.Typing.Core (at-most-counts 3) opTime noWitnesses

------------------------------------------------------------------------
-- Effectful computations
--
-- A computation's grade counts the operations along it.

sampling : [] ⊢C⦂ Reading ‼ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ
sampling =
  perform read ⋆                     -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
    (return here)

storing : [] ⊢C⦂ Unit ‼ ⟪ upto 1 , upto 1 , upto 0 ⟫ᵐ
storing =
  perform read ⋆                     -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
    (perform write here              -- ⟨ ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⟩ ∷ Unit
      (return ⋆))

relaying : [] ⊢C⦂ Unit ‼ ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ
relaying =
  perform read ⋆                     -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
    (perform send here               -- ⟨ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ⟩ ∷ Unit
      (return ⋆))

------------------------------------------------------------------------
-- Readings survive idling, not an operation

-- the reading is transmitted after idling five ticks, which count
-- nothing, so `var`'s bound holds on every counter

idle-then-transmit : [] ⊢C⦂ Unit ‼ ⟪ upto 1 , upto 0 , upto 1 ⟫ᵐ
idle-then-transmit =
  perform read ⋆                     -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
    (delay 5                         -- ⟨ ⟪ upto 0 , upto 0 , upto 0 ⟫ᵐ ⟩
      (perform send (fresh-var (≤! , ≤! , ≤! , tt) (Tl-⟨⟩ Hd))
                                     -- ⟨ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ⟩ ∷ Unit
        (return ⋆)))

-- storing the reading first makes it stale for the transmission

stale-after-storing : ¬ (uᵣ ·ᵣ opTime write ≾ᵣ uᵣ)
stale-after-storing (_ , wrote , _ , _) = ≰! wrote

-- and so a reading cannot be transmitted twice

stale-after-transmitting : ¬ (uᵣ ·ᵣ opTime send ≾ᵣ uᵣ)
stale-after-transmitting (_ , _ , sent , _) = ≰! sent

------------------------------------------------------------------------
-- A rate limit
--
-- At most two transmissions, and reads and writes unrestricted.

rate-limit : E
rate-limit = ⟪ unlimited , unlimited , upto 2 ⟫ᵐ

-- two uplinks keep it

two-uplinks : [] ⊢C⦂ Unit ‼ rate-limit
two-uplinks =
  coerce (tt , tt , ≤! , tt)
    (perform read ⋆                  -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
      (perform send here             -- ⟨ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ⟩ ∷ Unit
        (perform read ⋆              -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
          (perform send here         -- ⟨ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ⟩ ∷ Unit
            (return ⋆)))))

-- three are a program, graded by what they do

three-uplinks : [] ⊢C⦂ Unit ‼ ⟪ upto 3 , upto 0 , upto 3 ⟫ᵐ
three-uplinks =
  perform read ⋆ (perform send here
    (perform read ⋆ (perform send here
      (perform read ⋆ (perform send here (return ⋆))))))

-- and that grade breaks the limit on the transmission counter

three-break-the-limit : ¬ (⟪ upto 3 , upto 0 , upto 3 ⟫ᵐ ≾ₑ rate-limit)
three-break-the-limit (_ , _ , third , _) = ≰! third

-- however many reads and stores come with them

reads-are-free : ⟪ upto 9 , upto 9 , upto 2 ⟫ᵐ ≾ₑ rate-limit
reads-are-free = tt , tt , ≤! , tt

------------------------------------------------------------------------
-- Unboxing: a licence
--
-- `unbox`'s premise `elapsed ≾ᵣ ρ` counts the operations performed since
-- boxing against the box's quota. This licence covers one transmission,
-- and anything else.

licence : R
licence = ⟪ unlimited , unlimited , upto 1 ⟫ᵐ

-- a reading licensed this way is transmitted twice: claimed once before
-- the first transmission and once after it

sent-twice : [] ⊢C⦂ Unit ‼ ⟪ upto 0 , upto 0 , upto 2 ⟫ᵐ
sent-twice =
  box licence (const 42)             -- ∷ [ licence ] Reading
    (unbox Hd (tt , tt , ≤! , tt) (<:ᵛ-refl _)
                                     -- ∷ Reading
      (perform send here             -- ⟨ ⟪ upto 0 , upto 0 , upto 1 ⟫ᵐ ⟩ ∷ Unit
        (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) (tt , tt , ≤! , tt) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

-- a third claim, after the second transmission, is refused

a-third-claim : ¬ (uᵣ ·ᵣ opTime send ·ᵣ opTime send ≾ᵣ licence)
a-third-claim (_ , _ , second , _) = ≰! second

-- idling and local work leave the licence as it was

claim-after-a-long-wait : [] ⊢C⦂ Unit ‼ ⟪ upto 1 , upto 1 , upto 1 ⟫ᵐ
claim-after-a-long-wait =
  box licence (const 42)             -- ∷ [ licence ] Reading
    (delay 100                       -- ⟨ ⟪ upto 0 , upto 0 , upto 0 ⟫ᵐ ⟩
      (perform read ⋆                -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
        (perform write here          -- ⟨ ⟪ upto 0 , upto 1 , upto 0 ⟫ᵐ ⟩ ∷ Unit
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-⟨⟩ Hd))))) (tt , tt , ≤! , tt)
                 (<:ᵛ-refl _)        -- ∷ Reading
            (perform send here (return ⋆))))))

------------------------------------------------------------------------
-- Conditional branching
--
-- The join is the greater quota on each counter, so the conditional
-- below is charged a store and a transmission, though each run
-- performs one of them.

branching : [] ∷ Bool ∷ Reading ⊢C⦂ Unit ‼ ⟪ upto 0 , upto 1 , upto 1 ⟫ᵐ
branching =
  if eternal-var Boolₑ (Tl-∷ Hd)
    `then coerce (≤! , ≤! , ≤! , tt) (perform send  here (return ⋆))
    `else coerce (≤! , ≤! , ≤! , tt) (perform write here (return ⋆))

-- neither branch's own grade will do for the other

storing-is-not-transmitting : ¬ (opTime write ·ₑ uₑ ≾ₑ opTime send)
storing-is-not-transmitting (_ , wrote , _ , _) = ≰! wrote

------------------------------------------------------------------------
-- Effect handling
--
-- `handle` is graded by the handled computation's grade whatever the
-- clauses do, so suppressing the operations spends the quota all the
-- same.

nothing-fits : (op : Op) → (ε'' : E) → uₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' = uᵛ-least uₒ-least (op-grade op ·ₑ ε'')

suppressed : [] ⊢C⦂ Unit ‼ ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ
suppressed =
  handle perform read ⋆ (perform send here (perform send (const 0) (return ⋆)))
    `with discarding {[]} nothing-fits
    `in                              -- ⟨ ⟪ upto 1 , upto 0 , upto 2 ⟫ᵐ ⟩ ∷ Unit
      (return ⋆)

forwarded : [] ⊢C⦂ Reading ‼ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ
forwarded =
  handle perform read ⋆ (return here)
    `with forwarding {[]}
    `in                              -- ⟨ ⟪ upto 1 , upto 0 , upto 0 ⟫ᵐ ⟩ ∷ Reading
      (return here)

-- the barrier `⊤ᵣ` is unlimited on every counter, so no clause may
-- close over a reading

reading-stale-at-⊤ : ¬ (uᵣ ·ᵣ ⊤ᵣ ≾ᵣ uᵣ)
reading-stale-at-⊤ (() , _)

no-reporting : (op : Op) → (ε'' : E)
             → ¬ (uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ)
no-reporting op ε'' bound =
  reading-stale-at-⊤
    (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ} {op-grade op}
      (≾ᵣ-zero-productˡ {uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op} {ε''} bound))
