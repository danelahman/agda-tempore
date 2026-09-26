------------------------------------------------------------------------
-- A grade system in which the resource grades keep only a lower      --
-- bound.                                                             --
--                                                                    --
-- The effect grades are two-sided time intervals, bounding the       --
-- running time of a computation from both sides; the resource grades --
-- are left-sided intervals. The projection forgets the upper         --
-- endpoint, so a resource grade states only for how long data is     --
-- guaranteed to have been available.                                 --
--                                                                    --
-- Both greatest grades are non-absorbing, `[ 0 , ∞ ]` above and      --
-- `[ 0 ,+∞⟩` below, each the unit in the endpoint the projection     --
-- keeps, and the projection sends one to the other.                  --
------------------------------------------------------------------------

module Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals where

open import Data.Product

open import Syntax.Grades
open import Syntax.Grades.Example.Time.LeftSided
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity

open import Util.Equality

tsi→lsi : two-sided-intervals-with-∞ →ᵍ left-sided-intervals
tsi→lsi = record
  { map          = λ tsi → [ min tsi ,+∞⟩
  ; map-monotone = λ rel → proj₁ rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-of-nat   = refl
  }

twoSidedIntervalsToLeftSidedIntervalsGradeSystem : GradeSystem
twoSidedIntervalsToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals
  ; EGrade = two-sided-intervals-with-∞
  ; ∣_∣ᵉ   = tsi→lsi
  }
