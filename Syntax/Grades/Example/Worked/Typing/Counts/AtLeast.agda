------------------------------------------------------------------------
-- Typed example computations at certain counts of the operations.    --
--                                                                    --
-- Effect grades and resource grades are both `⟪ r , w , s ⟫ˡ`, "at   --
-- least `r` reads, `w` writes and `s` sends", and each operation is  --
-- graded by one draw on its own counter. Idling draws on none.       --
--                                                                    --
-- As a resource grade, `[ ⟪ r , w , s ⟫ˡ ] A` is a token that        --
-- becomes available once that many operations have certainly been    --
-- performed since boxing. It behaves as the lower bounds on time do, --
-- except that time does not stand in for operations: no amount of    --
-- idling makes a token available, as shown below.                    --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
--                                                                    --
--   * the bound `ρ ≾ᵣ uᵣ` of `var` holds at every `ρ`, demanding     --
--     nothing being the greatest grade: no reading goes stale.       --
--                                                                    --
--   * a handler clause cannot discard its continuation: a `return`   --
--     performs none of the operation it stands for.                  --
--                                                                    --
-- Every claim is checked counter by counter with `≤!`; a refutation  --
-- names the counter that falls short.                                --
--                                                                    --
-- The comments inside the programs state what each former appends to --
-- the context in which its subcomputation is typed: `⟨ ρ ⟩` a lock,  --
-- `∷ A` a binding.                                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing.Counts.AtLeast where

open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec.Base using ([]) renaming (_∷_ to _∷ᵛ_)

open import Relation.Nullary using (¬_)

open import Syntax.Grades.Example.Time.LeftSided using ([_,+∞⟩)
open import Syntax.Grades.Example.Counts.AtLeast using (at-least-counts)

open import Syntax.Grades.Example.Worked.Operations
  using (Op; read; write; send)
open import Syntax.Grades.Example.Worked.Counts.Index
  using (Certain; ⟪_,_,_⟫ˡ)

open import Syntax.Grades.Example.Worked.Time.Decide using (≤!; ≰!)

------------------------------------------------------------------------
-- The operations, each drawing once on its own counter

opTime : Op → Certain
opTime read  = ⟪ 1 , 0 , 0 ⟫ˡ
opTime write = ⟪ 0 , 1 , 0 ⟫ˡ
opTime send  = ⟪ 0 , 0 , 1 ⟫ˡ

open import Syntax.Grades.Example.System.Identity using (noWitnesses)
open import Syntax.Grades.Example.Worked.Typing.Core (at-least-counts 3) opTime noWitnesses

------------------------------------------------------------------------
-- Effectful computations

sampling : [] ⊢C⦂ Reading ‼ ⟪ 1 , 0 , 0 ⟫ˡ
sampling =
  perform read ⋆                     -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
    (return here)

relaying : [] ⊢C⦂ Unit ‼ ⟪ 1 , 0 , 1 ⟫ˡ
relaying =
  perform read ⋆                     -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
    (perform send here               -- ⟨ ⟪ 0 , 0 , 1 ⟫ˡ ⟩ ∷ Unit
      (return ⋆))

------------------------------------------------------------------------
-- Nothing goes stale

nothing-goes-stale : (ρ : R) → ρ ≾ᵣ uᵣ
nothing-goes-stale ([ _ ,+∞⟩ ∷ᵛ [ _ ,+∞⟩ ∷ᵛ [ _ ,+∞⟩ ∷ᵛ []) = ≤! , ≤! , ≤! , tt

-- a reading transmitted after a store and a transmission of its own

transmitted-late : [] ⊢C⦂ Unit ‼ ⟪ 1 , 1 , 2 ⟫ˡ
transmitted-late =
  perform read ⋆                     -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
    (perform write here              -- ⟨ ⟪ 0 , 1 , 0 ⟫ˡ ⟩ ∷ Unit
      (perform send (const 0)        -- ⟨ ⟪ 0 , 0 , 1 ⟫ˡ ⟩ ∷ Unit
        (perform send (fresh-var (nothing-goes-stale _)
                                 (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))))
                                     -- ⟨ ⟪ 0 , 0 , 1 ⟫ˡ ⟩ ∷ Unit
          (return ⋆))))

------------------------------------------------------------------------
-- Unboxing: a token earned by work
--
-- An average over three readings, available once three readings have
-- certainly been taken since it was boxed.

average : R
average = ⟪ 3 , 0 , 0 ⟫ˡ

-- claimed after three readings, a transmission in between: the other
-- counters demand nothing

claim-after-three-readings : [] ⊢C⦂ Unit ‼ ⟪ 3 , 0 , 2 ⟫ˡ
claim-after-three-readings =
  box {ρ = average} (const 42)       -- ∷ [ average ] Reading
    (perform read ⋆                  -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
      (perform send here             -- ⟨ ⟪ 0 , 0 , 1 ⟫ˡ ⟩ ∷ Unit
        (perform read ⋆              -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
          (perform read ⋆            -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
            (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))))))))
                   (≤! , ≤! , ≤! , tt) (<:ᵛ-refl _)
                                     -- ∷ Reading
              (perform send here (return ⋆)))))))

-- after two readings it is not yet available

two-readings-short : ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime read ≾ᵣ average)
two-readings-short (short , _) = ≰! short

-- and no amount of idling makes up the third

idling-is-no-reading :
  ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime read ·ᵣ of-durʳ 100 ≾ᵣ average)
idling-is-no-reading (short , _) = ≰! short

-- nor does a transmission

transmitting-is-no-reading :
  ¬ (uᵣ ·ᵣ opTime read ·ᵣ opTime read ·ᵣ opTime send ≾ᵣ average)
transmitting-is-no-reading (short , _) = ≰! short

------------------------------------------------------------------------
-- Joining branches
--
-- The join keeps only what both branches make certain, so a token
-- claimed after a conditional has to be earned on both paths.

three-readings-or-one : [] ∷ Bool ⊢C⦂ Unit ‼ ⟪ 1 , 0 , 0 ⟫ˡ
three-readings-or-one =
  if eternal-var Boolₑ Hd
    `then coerce (≤! , ≤! , ≤! , tt)
            (perform read ⋆ (perform read ⋆ (perform read ⋆ (return ⋆))))
    `else coerce (≤! , ≤! , ≤! , tt)
            (perform read ⋆ (perform send here (return ⋆)))

-- sequenced after it, the average is out of reach on either path

one-reading-certain : ¬ (uᵣ ·ᵣ ⟪ 1 , 0 , 0 ⟫ˡ ≾ᵣ average)
one-reading-certain (short , _) = ≰! short

------------------------------------------------------------------------
-- Effect handling

-- no clause may drop its continuation

no-discarding : ¬ (uₑ ≾ₑ op-grade read ·ₑ uₑ)
no-discarding (short , _) = ≰! short

-- and a clause may close over a reading: `⊤ᵣ` demands nothing, so
-- `var`'s bound holds at the barrier and past it

reading-crosses-the-barrier :
  (op : Op) → (ε'' : E) → uᵣ ·ᵣ ⊤ᵣ ·ᵣ op-grade op ·ᵣ ε'' ≾ᵣ uᵣ
reading-crosses-the-barrier op ε'' = nothing-goes-stale _

reported : Node ⊢C⦂ Reading ‼ ⟪ 1 , 0 , 0 ⟫ˡ
reported =
  handle perform read ⋆ (return here)
    `with reporting reading-crosses-the-barrier
    `in                              -- ⟨ ⟪ 1 , 0 , 0 ⟫ˡ ⟩ ∷ Reading
      (return here)
