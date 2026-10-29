------------------------------------------------------------------------
-- Right-sided time paired with an energy budget.                     --
--                                                                    --
-- The energy grade `[0, e ]` states "at most `e` units spent". It    --
-- has the carrier, sum, order, join and `⊤ = [0, ∞ ]` of the         --
-- right-sided intervals, with `of-dur` constantly `[0, ↑ 0 ]`:       --
-- `delay` spends time and no energy, and energy is spent by          --
-- operations alone.                                                  --
--                                                                    --
-- A grade `([0, n ] , [0, e ])` states "at most `n` steps and at     --
-- most `e` units". As a resource grade, a value boxed at it can be   --
-- unboxed only while at most `n` steps have passed and at most `e`   --
-- units have been spent since boxing, as for a calibration that      --
-- drifts with time and with use. A variable that is not eternal goes --
-- stale after any step or any expenditure of energy.                 --
--                                                                    --
-- The unit is least and `_·_` commutes; its hints declare both.      --
------------------------------------------------------------------------

module Grades.Examples.Product.RightSidedTimeEnergy where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (posetᵍ; Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Examples.Time.RightSided
  using ([0,_]; ↑_; right-sided-intervals; right-sided-intervalsʰ)

open import Util.Equality

-- energy: at most so many units, idling free

energy : Grade ℕᴰ
energy = record
  { Carrier         = R.Carrier
  ; _·_             = R._·_
  ; u               = R.u
  ; _≾_             = R._≾_
  ; ⊤               = R.⊤
  ; _⊔_             = R._⊔_
  ; of-dur          = λ _ → [0, ↑ 0 ]
  ; ·-identityˡ     = R.·-identityˡ
  ; ·-identityʳ     = R.·-identityʳ
  ; ·-assoc         = R.·-assoc
  ; ≾-refl          = λ {c} → R.≾-refl {c}
  ; ≾-trans         = λ {c} {d} {e} → R.≾-trans {c} {d} {e}
  ; ≾-irrelevant    = λ {c} {d} → R.≾-irrelevant {c} {d}
  ; _≾?_            = R._≾?_
  ; ≾-⊤             = R.≾-⊤
  ; ⊔-ubˡ           = R.⊔-ubˡ
  ; ⊔-ubʳ           = R.⊔-ubʳ
  ; ⊔-lub           = λ {c} {d} {e} → R.⊔-lub {c} {d} {e}
  ; ·-monoˡ-≾       = λ {c} {d} {e} → R.·-monoˡ-≾ {c} {d} {e}
  ; ·-monoʳ-≾       = λ {c} {d} {e} → R.·-monoʳ-≾ {c} {d} {e}
  ; ·-distribˡ-⊔-≾  = R.·-distribˡ-⊔-≾
  ; ·-distribʳ-⊔-≾  = R.·-distribʳ-⊔-≾
  ; ≾-zero-productˡ = λ {c} {d} → R.≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → R.≾-zero-productʳ {c} {d}
  ; of-dur-zero     = R.≃-refl
  ; of-dur-plus     = R.≃-refl
  ; ≃⇒≡?            = R.≃⇒≡?
  }
  where module R = Grade right-sided-intervals

-- its hints, those of right-sided time

energyʰ : GradeHints energy
energyʰ = record { u-least? = R.u-least? ; ·-comm? = R.·-comm? ; plus? = R.plus? }
  where module R = GradeHints right-sided-intervalsʰ

right-sided-time×energy : Grade ℕᴰ
right-sided-time×energy = right-sided-intervals ×ᵍ energy

right-sided-time×energyʰ : GradeHints right-sided-time×energy
right-sided-time×energyʰ = right-sided-intervalsʰ ×ʰ energyʰ
