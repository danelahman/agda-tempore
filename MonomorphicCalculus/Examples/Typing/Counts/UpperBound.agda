------------------------------------------------------------------------
-- Typed example computations at upper bounds on counts by name.      --
--                                                                    --
-- Effect grades and resource grades are both maps from operation     --
-- names to quotas, a default bounding the operations not listed;     --
-- each operation is graded by one draw on its own name, and idling   --
-- draws on none. A quota listing only transmissions bounds reads by  --
-- its default: with the default 0 a reading is refused, with the     --
-- default `unlimited` it is free.                                    --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
-- a reading survives idling and goes stale after an operation, and a --
-- handler clause may discard its continuation, the unit being least. --
--                                                                    --
-- Every side condition is discharged by the decision procedure of    --
-- the grade (`decided`, `check`), and every refutation by it         --
-- (`refuted`).                                                       --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.Counts.UpperBound where

open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.Time.RightSided using (𝟏ₒ-least)
open import Grades.Examples.Counts.AtMost using (upto; unlimited)
open import Grades.Examples.Counts.UpperBound using (counts-upper-bound)
open import Grades.Examples.Worked.Counts.UpperBound using (single)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)

open Maps ℕ-names using (pointwise⁺) renaming (_!_ to _!ᵐ_)

------------------------------------------------------------------------
-- The operations, each drawing once on its own name

opTime : Op → Grade.Carrier counts-upper-bound
opTime read  = single read (upto 1) (upto 0)
opTime write = single write (upto 1) (upto 0)
opTime send  = single send (upto 1) (upto 0)

open import MonomorphicCalculus.Examples.Typing.Core counts-upper-bound opTime

-- side conditions, decided

decided : ∀ {c d : R} {p : True (c ≾ᵣ? d)} → c ≾ᵣ d
decided {p = p} = toWitness p

refuted : (c d : R) {p : False (c ≾ᵣ? d)} → ¬ (c ≾ᵣ d)
refuted c d {p} = toWitnessFalse p

check : ∀ {Γ A ε} (ε' : E) {p : True (ε ≾ₑ? ε')} → Γ ⊢ᶜ⦂ A ! ε → Γ ⊢ᶜ⦂ A ! ε'
check ε' {p} M = coerce (toWitness p) M

------------------------------------------------------------------------
-- A rate limit by name
--
-- At most two transmissions, every other operation free.

rate-limit : E
rate-limit = single send (upto 2) unlimited

two-uplinks : [] ⊢ᶜ⦂ unit ! rate-limit
two-uplinks =
  check rate-limit
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (perform send here             -- ⟨ opTime send ⟩ ∷ unit
        (perform read ⋆              -- ⟨ opTime read ⟩ ∷ Reading
          (perform send here         -- ⟨ opTime send ⟩ ∷ unit
            (return ⋆)))))

-- three transmissions break it

three-uplinks : E
three-uplinks = opTime send ·ₑ opTime send ·ₑ opTime send

three-break-the-limit : ¬ (three-uplinks ≾ₑ rate-limit)
three-break-the-limit = refuted three-uplinks rate-limit

-- a limit listing only transmissions, its default 0, forbids reading

sends-only : E
sends-only = single send (upto 2) (upto 0)

reading-forbidden : ¬ (opTime read ·ₑ opTime send ≾ₑ sends-only)
reading-forbidden = refuted (opTime read ·ₑ opTime send) sends-only

------------------------------------------------------------------------
-- Readings survive idling, not an operation

idle-then-transmit : [] ⊢ᶜ⦂ unit ! rate-limit
idle-then-transmit =
  check rate-limit
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (delay 5                       -- ⟨ 𝟏ᵣ ⟩
        (perform send (fresh-var decided (Tl-⟨⟩ Hd))
                                     -- ⟨ opTime send ⟩ ∷ unit
          (return ⋆))))

stale-after-storing : ¬ (𝟏ᵣ ·ᵣ opTime write ≾ᵣ 𝟏ᵣ)
stale-after-storing = refuted (𝟏ᵣ ·ᵣ opTime write) 𝟏ᵣ

------------------------------------------------------------------------
-- Unboxing: a licence for one transmission, anything else free

licence : R
licence = single send (upto 1) unlimited

sent-twice : [] ⊢ᶜ⦂ unit ! single send (upto 2) (upto 0)
sent-twice =
  check (single send (upto 2) (upto 0))
    (box licence (const reading 42)  -- ∷ [ licence ] Reading
      (unbox Hd decided (<:ᵛ-refl _) -- ∷ Reading
        (perform send here           -- ⟨ opTime send ⟩ ∷ unit
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ Hd))) decided (<:ᵛ-refl _)
                                     -- ∷ Reading
            (perform send here (return ⋆))))))

-- a third claim, after the second transmission, is refused

a-third-claim : ¬ (𝟏ᵣ ·ᵣ opTime send ·ᵣ opTime send ≾ᵣ licence)
a-third-claim = refuted (𝟏ᵣ ·ᵣ opTime send ·ᵣ opTime send) licence

-- reading and storing leave the licence as it was

claim-after-local-work : [] ⊢ᶜ⦂ unit ! rate-limit
claim-after-local-work =
  check rate-limit
    (box licence (const reading 42)  -- ∷ [ licence ] Reading
      (perform read ⋆                -- ⟨ opTime read ⟩ ∷ Reading
        (perform write here          -- ⟨ opTime write ⟩ ∷ unit
          (unbox (Tl-∷ (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd)))) decided (<:ᵛ-refl _)
                                     -- ∷ Reading
            (perform send here (return ⋆))))))

------------------------------------------------------------------------
-- Effect handling: the unit is least, so a clause may discard its
-- continuation

nothing-fits : (op : Op) → (ε'' : E) → 𝟏ₑ ≾ₑ op-grade op ·ₑ ε''
nothing-fits op ε'' = pointwise⁺ _ (λ s → 𝟏ₒ-least ((op-grade op ·ₑ ε'') !ᵐ s))

suppressed : [] ⊢ᶜ⦂ unit ! rate-limit
suppressed =
  check rate-limit
    (handle perform read ⋆ (perform send here (return ⋆))
      `with discarding {[]} nothing-fits
      `in                            -- ⟨ opTime read · opTime send ⟩ ∷ unit
        (return ⋆))
