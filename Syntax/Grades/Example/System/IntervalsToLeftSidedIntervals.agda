------------------------------------------------------------------------
-- A grade system in which the resource grades keep only a lower bound. --
--                                                                     --
-- Effect grades are two-sided time intervals, bounding a computation's --
-- running time from both sides; resource grades are left-sided         --
-- intervals, which keep the lower bound alone. The projection forgets  --
-- the upper endpoint, so a resource grade says only how long data is   --
-- guaranteed to have been available for.                               --
------------------------------------------------------------------------

module Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals where

open import Data.Product

open import Syntax.Grades
open import Syntax.Grades.Example.Interval.LeftSided
open import Syntax.Grades.Example.Interval.TwoSided

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
