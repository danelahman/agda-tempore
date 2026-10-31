------------------------------------------------------------------------
-- Typed example computations over the duration-hull system of the    --
-- rigid regular-expression upper bounds, in dense time.              --
--                                                                    --
-- Effect grades are upper bounds over interval letters, each         --
-- operation graded by itself; resource grades are right-sided time   --
-- intervals, and an effect grade is measured by its slowest run. A   --
-- box with a deadline of three units may be opened after a reading   --
-- and a wait of a unit, at most one and a half units having passed;  --
-- after a reading and a transmission it may not, the transmission    --
-- possibly taking four. The effect grade records the run itself.     --
--                                                                    --
-- Reading takes more than a quarter and at most half a unit, writing --
-- one to two units, sending two to four.                             --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Rational.RightSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Examples.Time.Dense.RightSided
  using (ℚ≥0; [0,_]; ↑_; ∞; _/_; #_) renaming (_≤_ to _≤ᵈ_; _≤?_ to _≤ᵈ?_)

open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import MonomorphicCalculus.Examples.Typing.Traces.Rigid.Finite.TwoSided
  using (code; name; name-code; code-name; running)

import Grades.Examples.Traces.Rigid.Rational.RightSided Op 3 code name name-code code-name running as U
open import Grades.Examples.System.Traces.Rigid.Rational.RightSided Op 3 code name name-code code-name running
  using (upperRunsToRightSidedIntervalsGradeSystem)

open U using (Proper′; ‵_; _·_; _*; idle_; ≤_; upper)

-- comparisons of rationals, decided

≤ᵈ! : {p q : ℚ≥0} {w : True (p ≤ᵈ? q)} → p ≤ᵈ q
≤ᵈ! {w = w} = toWitness w

≰ᵈ! : {p q : ℚ≥0} {w : False (p ≤ᵈ? q)} → ¬ (p ≤ᵈ q)
≰ᵈ! {w = w} = toWitnessFalse w

------------------------------------------------------------------------
-- The operations, graded by themselves

opTime : Op → Proper′ upper
opTime read  = U.⌜ ‵_ {upper} read ⌝
opTime write = U.⌜ ‵_ {upper} write ⌝
opTime send  = U.⌜ ‵_ {upper} send ⌝

open import MonomorphicCalculus.Examples.Typing.System
  upperRunsToRightSidedIntervalsGradeSystem opTime
  hiding (_/_)

------------------------------------------------------------------------
-- A box with a deadline of three units

three-units : R
three-units = [0, ↑ # 3 ]

-- opened after a reading and a wait of a unit: at most one and a half
-- units have passed

in-time : [] ⊢C⦂ unit ! _
in-time =
  box three-units (const reading 42) -- ∷ [ three-units ] Reading
    (perform read ⋆          -- ⟨ ∣ opTime read ∣ ⟩ ∷ Reading
      (delay (# 1)           -- ⟨ ι 1 ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤ᵈ! (<:ᵛ-refl _)
                             -- ∷ Reading
          (perform write here (return ⋆)))))

-- after a reading and a transmission, up to four and a half units may
-- have passed

too-late : ¬ (𝟏ᵣ ·ᵣ ∣ opTime read ∣ᵉ ·ᵣ ∣ opTime send ∣ᵉ ≾ᵣ three-units)
too-late = ≰ᵈ!

-- the effect grade of the run is the run itself, measured by its
-- slowest instance: half a unit, a unit, two units

run : E
run = opTime read ·ₑ (U.⌜ idle ≤ (# 1) ⌝ ·ₑ opTime write)

run-measured : ∣ run ∣ᵉ ≡ [0, ↑ 7 / 2 ]
run-measured = refl

run-is-delayed : run ≃ₑ opTime read ·ₑ (ιₑ (# 1) ·ₑ opTime write)
run-is-delayed = ≃ₑ-refl

-- readings repeated any number of times have no deadline

readings : E
readings = U.⌜ ‵ read * ⌝

readings-measured : ∣ readings ∣ᵉ ≡ [0, ∞ ]
readings-measured = refl
