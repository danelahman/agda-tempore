------------------------------------------------------------------------
-- Typed example computations at the windowed schedules.              --
--                                                                    --
-- Effect grades and resource grades are both a set of durations and, --
-- for each operation, the times at which it happens. A reading takes --
-- one step, storing two or three, transmitting four to six, each     --
-- happening at its own start; `delay n` takes `n` steps and does     --
-- nothing.                                                           --
--                                                                    --
-- A schedule that lets the radio warm up for three steps admits an   --
-- uplink that idles two steps between reading and transmitting, and  --
-- refuses one that transmits at once. A box graded "within four      --
-- steps, anything at any time" is a value that goes stale: it is     --
-- claimed after idling three steps, and refused after five.          --
--                                                                    --
-- The two rules that place the unit on opposite sides of the order:  --
-- the unit takes no time, so a reading goes stale after any step,    --
-- idling included; and it is not least, so a handler clause cannot   --
-- discard its continuation.                                          --
--                                                                    --
-- Every side condition is discharged by the decision procedure of    --
-- the grade (`decided`, `check`), and every refutation by it         --
-- (`refuted`).                                                       --
------------------------------------------------------------------------

module ClosedCalculus.Examples.Typing.SemiDirect.WindowedSchedules where

open import Data.Nat.Base using (ℕ; suc; _+_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

import Data.List.Base as L

open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.SemiDirect.WindowedSchedules
  using (windowed-schedules; durations; Durations; Times; ⟪_⟫ₜ; _∪ₜ_; ∅ₜ; ℕₜ)
open import Grades.Examples.Worked.SemiDirect.WindowedSchedules
  using (name; span; window)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import Grades.Examples.System.Identity using (noWitnesses)

open Maps ℕ-names using (Map; _∣_)
open Grade durations using (of-dur)

-- taking `T`, performing `o` only at times `E`

at : Durations → Op → Times → Grade.Carrier windowed-schedules
at T o E = T , (∅ₜ ∣ ((name o , E) L.∷ L.[]))

------------------------------------------------------------------------
-- The operations, each happening at its start

opTime : Op → Grade.Carrier windowed-schedules
opTime read  = at (of-dur 1)  read  ⟪ 0 ⟫ₜ
opTime write = at (span 2 1)  write ⟪ 0 ⟫ₜ
opTime send  = at (span 4 2)  send  ⟪ 0 ⟫ₜ

open import ClosedCalculus.Examples.Typing.Core windowed-schedules opTime noWitnesses

-- the grades are given: a meta for one would be eta-expanded into its
-- table before the decision could run

decided : (c d : R) {p : True (c ≾ᵣ? d)} → c ≾ᵣ d
decided c d {p} = toWitness p

refuted : (c d : R) {p : False (c ≾ᵣ? d)} → ¬ (c ≾ᵣ d)
refuted c d {p} = toWitnessFalse p

check : ∀ {Γ A ε} (ε' : E) {p : True (ε ≾ₑ? ε')} → Γ ⊢C⦂ A ‼ ε → Γ ⊢C⦂ A ‼ ε'
check ε' {p} M = coerce (toWitness p) M

------------------------------------------------------------------------
-- A schedule: within ten steps, reading at the start, and the radio
-- warming up for three steps

warm-up : E
warm-up = span 0 10 , (∅ₜ ∣ ((name read , ⟪ 0 ⟫ₜ) L.∷ (name send , window 3 7) L.∷ L.[]))

-- an uplink with a constant payload, idling two steps first

late-uplink : [] ⊢C⦂ Reading ‼ warm-up
late-uplink =
  check warm-up
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (delay 2                       -- ⟨ of-dur 2 ⟩
        (perform send (const 0)      -- ⟨ opTime send ⟩ ∷ Unit
          (return (const 1)))))

-- transmitting at once is a program, graded by what it does

early : E
early = opTime read ·ₑ (opTime send ·ₑ uₑ)

early-uplink : [] ⊢C⦂ Unit ‼ early
early-uplink =
  check early
    (perform read ⋆                  -- ⟨ opTime read ⟩ ∷ Reading
      (perform send here             -- ⟨ opTime send ⟩ ∷ Unit
        (return ⋆)))

-- and that grade transmits at time 1, before the radio is warm

early-refused : ¬ (early ≾ₑ warm-up)
early-refused = refuted early warm-up

------------------------------------------------------------------------
-- Readings go stale after any step, idling included

stale-after-idling : ¬ (uᵣ ·ᵣ of-durʳ 1 ≾ᵣ uᵣ)
stale-after-idling = refuted (uᵣ ·ᵣ of-durʳ 1) uᵣ

------------------------------------------------------------------------
-- Unboxing: a value that goes stale after four steps

within-four : R
within-four = span 0 4 , (ℕₜ ∣ L.[])

-- claimed after idling three steps: seven to nine steps, transmitting
-- at time 3

claimed-in-time : [] ⊢C⦂ Unit ‼ at (span 7 2) send ⟪ 3 ⟫ₜ
claimed-in-time =
  check (at (span 7 2) send ⟪ 3 ⟫ₜ)
    (box within-four (const 42)      -- ∷ [ within-four ] Reading
      (delay 3                       -- ⟨ of-dur 3 ⟩
        (unbox (Tl-⟨⟩ Hd) (decided (uᵣ ·ᵣ of-durʳ 3) within-four) (<:ᵛ-refl _)
                                     -- ∷ Reading
          (perform send here (return ⋆)))))

claimed-too-late : ¬ (uᵣ ·ᵣ of-durʳ 5 ≾ᵣ within-four)
claimed-too-late = refuted (uᵣ ·ᵣ of-durʳ 5) within-four

-- after a reading and a store, which take three or four steps, it is
-- still in time

claimed-after-storing : uᵣ ·ᵣ opTime read ·ᵣ opTime write ≾ᵣ within-four
claimed-after-storing = decided (uᵣ ·ᵣ opTime read ·ᵣ opTime write) within-four

------------------------------------------------------------------------
-- Effect handling: the unit is not least, so no clause discards its
-- continuation

cannot-discard : ¬ (uₑ ≾ₑ opTime read ·ₑ uₑ)
cannot-discard = refuted uₑ (opTime read ·ₑ uₑ)
