------------------------------------------------------------------------
-- Typed example computations at the mode times.                      --
--                                                                    --
-- Effect grades and resource grades are both mode times over two     --
-- modes of the node, `Idle` (mode 0) and `Radio` (mode 1), the radio --
-- on; the operations take their running times (`Worked.Operations`)  --
-- in the mode they start from. Reading works in every mode and keeps --
-- it; storing works only when idle; transmitting switches the radio  --
-- on from `Idle`, or transmits with it on. Idling keeps the mode and --
-- spends its time in it.                                             --
--                                                                    --
-- A deadline of twelve steps from `Idle` or `Radio`, never stuck     --
-- from them, admits a reading and a transmission and refuses a       --
-- second transmission, which may take thirteen; storing after a      --
-- transmission gets stuck and is refused. A box graded "within eight --
-- steps, in whichever mode" is claimed after idling five steps and   --
-- refused after nine.                                                --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
-- the unit spends no time, so a reading goes stale after any step,   --
-- idling included; and it is not least, so a handler clause cannot   --
-- discard its continuation.                                          --
--                                                                    --
-- Every side condition is discharged by the decision procedure of    --
-- the grade (`decided`, `check`), and every refutation by it         --
-- (`refuted`).                                                       --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.SemiDirect.ModeTimes where

open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

import Data.List.Base as L
open import Data.Product using (_,_)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.Time.TwoSidedWithInfinity using ([_,_]; ↑_; ∞)
open import Grades.Examples.SemiDirect.ModeTimes.Boxes using (witness)
open import Grades.Examples.SemiDirect.ModeTimes
  renaming (decided to grade)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)
  renaming (opTime to running)

open Maps ℕ-names using (_∣_)

Idle Radio : Point
Idle  = ⟨ 0 ⟩
Radio = ⟨ 1 ⟩

------------------------------------------------------------------------
-- The operations, each spending its running time in its start mode

opTime : Op → Grade.Carrier mode-times
opTime read  = occurrence ((⋆ , ⋆) L.∷ L.[]) (running read)
opTime write = occurrence ((Idle , Idle) L.∷ L.[]) (running write)
opTime send  = occurrence ((Idle , Radio) L.∷ (Radio , Radio) L.∷ L.[]) (running send)

open import ClosedCalculus.Examples.Typing.Core mode-times opTime

decided : (c d : R) {p : True (c ≾ᵣ? d)} → c ≾ᵣ d
decided c d {p} = toWitness p

refuted : (c d : R) {p : False (c ≾ᵣ? d)} → ¬ (c ≾ᵣ d)
refuted c d {p} = toWitnessFalse p

check : ∀ {Γ A ε} (ε' : E) {p : True (ε ≾ₑ? ε')} → Γ ⊢C⦂ A ‼ ε → Γ ⊢C⦂ A ‼ ε'
check ε' {p} M = coerce (toWitness p) M

------------------------------------------------------------------------
-- A deadline of twelve steps from `Idle` or `Radio`

deadline : E
deadline = listed (0 L.∷ 1 L.∷ L.[])
  (  (Idle , Idle , within)
  L.∷ (Idle , Radio , within)
  L.∷ (Radio , Radio , within)
  L.∷ (⋆ , ✗ , anytime)
  L.∷ L.[])
  where
    within  = bounds ([ 0 , ∞ ] ∣ L.[]) [ 0 , ↑ 12 ] (witness L.[] tt)
    anytime = bounds ([ 0 , ∞ ] ∣ L.[]) [ 0 , ∞ ] (witness L.[] tt)

sample-and-transmit : [] ⊢C⦂ Unit ‼ deadline
sample-and-transmit =
  check deadline
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (perform send here             -- ⟨ opTime send ⟩ ∷ Unit
        (return ⋆)))

-- a second transmission may take thirteen steps

two-transmissions : E
two-transmissions = opTime read ·ₑ (opTime send ·ₑ (opTime send ·ₑ uₑ))

two-transmissions-refused : ¬ (two-transmissions ≾ₑ deadline)
two-transmissions-refused = refuted two-transmissions deadline

-- storing after a transmission gets stuck

store-after-transmitting : E
store-after-transmitting = opTime send ·ₑ (opTime write ·ₑ uₑ)

store-after-transmitting-refused : ¬ (store-after-transmitting ≾ₑ deadline)
store-after-transmitting-refused = refuted store-after-transmitting deadline

------------------------------------------------------------------------
-- Readings go stale after any step, idling included

stale-after-idling : ¬ (uᵣ ·ᵣ of-durʳ 1 ≾ᵣ uᵣ)
stale-after-idling = refuted (uᵣ ·ᵣ of-durʳ 1) uᵣ

------------------------------------------------------------------------
-- Unboxing: within eight steps, in whichever mode

within-eight : R
within-eight = listed L.[]
  (  (⋆ , ⋆ , eight)
  L.∷ (⋆ , ⋆' , eight)
  L.∷ L.[])
  where
    eight = bounds ([ 0 , ∞ ] ∣ L.[]) [ 0 , ↑ 8 ] (witness L.[] tt)

claimed-in-time : [] ⊢C⦂ Reading ‼ (of-durᵉ 5 ·ₑ uₑ)
claimed-in-time =
  check (of-durᵉ 5 ·ₑ uₑ)
    (box within-eight (const 42)     -- ∷ [ within-eight ] Reading
      (delay 5                       -- ⟨ of-dur 5 ⟩
        (unbox (Tl-⟨⟩ Hd) (decided (uᵣ ·ᵣ of-durʳ 5) within-eight) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (return here))))

claimed-too-late : ¬ (uᵣ ·ᵣ of-durʳ 9 ≾ᵣ within-eight)
claimed-too-late = refuted (uᵣ ·ᵣ of-durʳ 9) within-eight

------------------------------------------------------------------------
-- Effect handling: the unit is not least, so no clause discards a
-- transmission's continuation

cannot-discard : ¬ (uₑ ≾ₑ opTime send ·ₑ uₑ)
cannot-discard = refuted uₑ (opTime send ·ₑ uₑ)
