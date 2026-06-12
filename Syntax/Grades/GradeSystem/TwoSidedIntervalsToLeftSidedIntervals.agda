----------------------------------------------------------------
-- Example grade system of two-sided time intervals as effect --
-- grades and left-sided time intervals as resource grades    --
----------------------------------------------------------------

module Syntax.Grades.GradeSystem.TwoSidedIntervalsToLeftSidedIntervals where

open import Data.Product

open import Syntax.Grades
open import Syntax.Grades.LeftSidedTimeIntervals
open import Syntax.Grades.TwoSidedTimeIntervals

open import Util.Equality

tsi→lsi : two-sided-intervals →ᵍ left-sided-intervals
tsi→lsi = record
  { map          = λ tsi → [ min tsi ,+∞⟩
  ; map-monotone = λ rel → proj₁ rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-of-nat   = refl
  }

twoSidedIntervalsToLeftSidedIntervalsGradeSystem : GradeSystem
twoSidedIntervalsToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals
  ; EGrade = two-sided-intervals
  ; ∣_∣ᵉ   = tsi→lsi
  }
