----------------------------------------------------------------
-- Example grade system of two-sided time intervals as effect --
-- grades and left-sided time intervals as resource grades    --
----------------------------------------------------------------

module Syntax.Grades.GradeSystem.TwoSidedToOneSidedTimeIntervals where

open import Data.Product

open import Syntax.Grades
open import Syntax.Grades.Time.LeftSidedIntervals
open import Syntax.Grades.Time.TwoSidedIntervals

open import Util.Equality

tsi→lsi : intervals →ᵍ one-sided-intervals
tsi→lsi = record
  { map          = λ tsi → [ min tsi ,+∞⟩
  ; map-monotone = λ rel → proj₁ rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-of-nat   = refl
  }

intGradeSystem : GradeSystem
intGradeSystem = record
  { RGrade = one-sided-intervals
  ; EGrade = intervals
  ; ∣_∣ᵉ   = tsi→lsi
  }
