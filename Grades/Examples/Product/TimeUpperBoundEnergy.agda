------------------------------------------------------------------------
-- Upper bounds on time paired with an energy budget.                 --
--                                                                    --
-- The energy grade `[0, e ]` states "at most `e` units spent". It    --
-- has the carrier, sum, order, join and `⊤ = [0, ∞ ]` of the         --
-- upper bounds, with `ι` constantly `[0, ↑ 0 ]`:                     --
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

module Grades.Examples.Product.TimeUpperBoundEnergy where

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (posetᵍ; Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Product using (_×ᵍ_; _×ʰ_)
open import Grades.Examples.Time.UpperBound
  using ([0,_]; ↑_; upper-bounds; upper-boundsʰ)

open import Util.Equality

-- energy: at most so many units, idling free

energy : Grade ℕᴰ
energy = record
  { Carrier         = R.Carrier
  ; _·_             = R._·_
  ; 𝟏               = R.𝟏
  ; _≾_             = R._≾_
  ; ⊤               = R.⊤
  ; _⊔_             = R._⊔_
  ; ι               = λ _ → [0, ↑ 0 ]
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
  ; ι-zero          = R.≃-refl
  ; ι-plus          = R.≃-refl
  }
  where module R = Grade upper-bounds

-- its hints, those of upper bounds on time

energyʰ : GradeHints energy
energyʰ = record { 𝟏-least? = R.𝟏-least? ; ·-comm? = R.·-comm? ; plus? = R.plus? }
  where module R = GradeHints upper-boundsʰ

time-upper-bound×energy : Grade ℕᴰ
time-upper-bound×energy = upper-bounds ×ᵍ energy

time-upper-bound×energyʰ : GradeHints time-upper-bound×energy
time-upper-bound×energyʰ = upper-boundsʰ ×ʰ energyʰ
