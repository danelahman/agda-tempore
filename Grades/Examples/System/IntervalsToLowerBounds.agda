------------------------------------------------------------------------
-- A grade system in which the resource grades keep only a lower      --
-- bound.                                                             --
--                                                                    --
-- The effect grades are time intervals, bounding the                 --
-- running time of a computation from both sides; the resource grades --
-- are lower bounds. The projection forgets the upper                 --
-- endpoint, so a resource grade states only for how long data is     --
-- guaranteed to have been available.                                 --
--                                                                    --
-- Both greatest grades are non-absorbing, `[ 0 , ∞ ]` above and      --
-- `[ 0 ,+∞⟩` below, each the unit in the endpoint the projection     --
-- keeps, and the projection sends one to the other.                  --
------------------------------------------------------------------------

module Grades.Examples.System.IntervalsToLowerBounds where

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Product
open import Data.Maybe.Base using (nothing)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Grades.Examples.Time.LowerBound
open import Grades.Examples.Time.Interval

open import Util.Equality

intervals→lower-bounds : interval →ᵍ lower-bound
intervals→lower-bounds = strictᵍ record
  { map          = λ i → [ min i ,+∞⟩
  ; map-monotone = λ rel → proj₁ rel
  ; map-𝟏        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-ι        = refl
  }

intervals→lower-bounds-grade-system : GradeSystem
intervals→lower-bounds-grade-system = record
  { RGrade = lower-bound
  ; EGrade = interval
  ; ∣-∣ᵉ   = intervals→lower-bounds
  }

-- its hints

intervals→lower-bounds-grade-systemʰ : SystemHints intervals→lower-bounds-grade-system
intervals→lower-bounds-grade-systemʰ = record
  { RHints      = lower-boundʰ
  ; EHints      = intervalʰ
  ; reflects-𝟏? = nothing
  ; witnesses   = λ _ _ _ → []ᴸ
  }
