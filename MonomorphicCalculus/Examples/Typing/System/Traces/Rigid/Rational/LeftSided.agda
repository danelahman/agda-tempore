------------------------------------------------------------------------
-- Typed example computations over the duration-hull system of the    --
-- rigid regular-expression lower bounds, in dense time.              --
--                                                                    --
-- Effect grades are lower bounds over interval letters, each         --
-- operation graded by itself; resource grades are left-sided time    --
-- intervals, and an effect grade is measured by its fastest run. A   --
-- box asking for a unit of time may be opened after a reading and a  --
-- wait of a unit, the reading's quarter adding to it; right after    --
-- the reading it may not. The effect grade records the run itself:   --
-- the reading, an undisturbed wait, and the store.                   --
--                                                                    --
-- Reading takes more than a quarter and at most half a unit, writing --
-- one to two units, sending two to four.                             --
------------------------------------------------------------------------

module MonomorphicCalculus.Examples.Typing.System.Traces.Rigid.Rational.LeftSided where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)

open import Util.Equality

open import Grades.Base using (module GradeMorphism)
open import Grades.Examples.Time.Dense.LeftSided
  using (ℚ≥0; [_,+∞⟩; _/_; #_) renaming (_≤_ to _≤ᵈ_; _≤?_ to _≤ᵈ?_)

open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import MonomorphicCalculus.Examples.Typing.Traces.Rigid.Finite.TwoSided
  using (code; name; name-code; code-name; running)

import Grades.Examples.Traces.Rigid.Rational.LeftSided Op 3 code name name-code code-name running as L
open import Grades.Examples.System.Traces.Rigid.Rational.LeftSided Op 3 code name name-code code-name running
  using (lowerRunsToLeftSidedIntervalsGradeSystem; lower-runs→left-sided-intervals)

open L using (Proper′; ‵_; _·_; idle_; ≥_; lower)

-- comparisons of rationals, decided

≤ᵈ! : {p q : ℚ≥0} {w : True (p ≤ᵈ? q)} → p ≤ᵈ q
≤ᵈ! {w = w} = toWitness w

≰ᵈ! : {p q : ℚ≥0} {w : False (p ≤ᵈ? q)} → ¬ (p ≤ᵈ q)
≰ᵈ! {w = w} = toWitnessFalse w

------------------------------------------------------------------------
-- The operations, graded by themselves

opTime : Op → Proper′ lower
opTime read  = L.⌜ ‵_ {lower} read ⌝
opTime write = L.⌜ ‵_ {lower} write ⌝
opTime send  = L.⌜ ‵_ {lower} send ⌝

open import MonomorphicCalculus.Examples.Typing.System
  lowerRunsToLeftSidedIntervalsGradeSystem opTime
  hiding (_/_)

------------------------------------------------------------------------
-- A box asking for a unit of time

a-unit : R
a-unit = [ # 1 ,+∞⟩

-- opened after a reading and a wait of a unit: at least a unit and a
-- quarter has passed

settled : [] ⊢ᶜ⦂ unit ! _
settled =
  box a-unit (const reading 42) -- ∷ [ a-unit ] Reading
    (perform read ⋆             -- ⟨ ∣ opTime read ∣ ⟩ ∷ Reading
      (delay (# 1)              -- ⟨ ι 1 ⟩
        (unbox (Tl-⟨⟩ (Tl-∷ (Tl-⟨⟩ Hd))) ≤ᵈ! (<:ᵛ-refl _)
                             -- ∷ Reading
          (perform write here (return ⋆)))))

-- right after the reading, only a quarter is certain to have passed

too-soon : ¬ (𝟏ᵣ ·ᵣ ∣ opTime read ∣ᵉ ≾ᵣ a-unit)
too-soon = ≰ᵈ!

-- the effect grade of the run is the run itself, measured by its
-- fastest instance: a quarter, a unit, a unit

run : E
run = opTime read ·ₑ (L.⌜ idle ≥ (# 1) ⌝ ·ₑ opTime write)

run-measured : ∣ run ∣ᵉ ≡ [ 9 / 4 ,+∞⟩
run-measured = refl

run-is-delayed : run ≃ₑ opTime read ·ₑ (ιₑ (# 1) ·ₑ opTime write)
run-is-delayed = ≃ₑ-refl
