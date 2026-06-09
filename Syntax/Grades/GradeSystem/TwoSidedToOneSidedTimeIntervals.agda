---------------------------------------------------------------------
-- Grade System of TSI as effect grades and LSI as resource grades --
---------------------------------------------------------------------

module Syntax.Grades.GradeSystem.TwoSidedToOneSidedTimeIntervals where

open import Data.Product

open import Syntax.Grades
open import Syntax.Grades.Time.LeftSidedIntervals
open import Syntax.Grades.Time.TwoSidedIntervals

open import Util.Equality

-- mapping two-sided intervals to one-sided-intervals (left):
-- project on LSI the minimum in TSI.

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
