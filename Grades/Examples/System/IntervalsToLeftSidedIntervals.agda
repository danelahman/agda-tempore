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

module Grades.Examples.System.IntervalsToLeftSidedIntervals where

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Product
open import Data.Maybe.Base using (nothing)

open import Grades.Base
open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Examples.Time.LeftSided
open import Grades.Examples.Time.TwoSidedWithInfinity

open import Util.Equality

tsi→lsi : two-sided-intervals-with-∞ →ᵍ left-sided-intervals
tsi→lsi = strictᵍ record
  { map          = λ tsi → [ min tsi ,+∞⟩
  ; map-monotone = λ rel → proj₁ rel
  ; map-u        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-of-dur   = refl
  }

twoSidedIntervalsToLeftSidedIntervalsGradeSystem : GradeSystem
twoSidedIntervalsToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals
  ; EGrade = two-sided-intervals-with-∞
  ; ∣_∣ᵉ   = tsi→lsi
  }

-- its hints

twoSidedIntervalsToLeftSidedIntervalsGradeSystemʰ : SystemHints twoSidedIntervalsToLeftSidedIntervalsGradeSystem
twoSidedIntervalsToLeftSidedIntervalsGradeSystemʰ = record
  { RHints      = left-sided-intervalsʰ
  ; EHints      = two-sided-intervals-with-∞ʰ
  ; reflects-u? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
