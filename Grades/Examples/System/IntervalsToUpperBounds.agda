------------------------------------------------------------------------
-- A grade system in which the resource grades keep only an upper     --
-- bound.                                                             --
--                                                                    --
-- The effect grades are time intervals, bounding the                 --
-- running time of a computation from both sides; the resource grades --
-- are upper bounds. The projection forgets the lower                 --
-- endpoint, so a resource grade states only by when data is          --
-- guaranteed to be available.                                        --
--                                                                    --
-- The greatest grades `[ 0 , ∞ ]` above and `[0, ∞ ]` below          --
-- correspond, the first non-absorbing and the second absorbing, and  --
-- the projection reflects the unit: an interval whose upper endpoint --
-- is 0 is `[ 0 , 0 ]`.                                               --
------------------------------------------------------------------------

module Grades.Examples.System.IntervalsToUpperBounds where

open import Data.List.Base using () renaming ([] to []ᴸ)
open import Data.Nat.Base using (z≤n)
open import Data.Product
open import Data.Maybe.Base using (just)

open import Grades.Base
open import Grades.Hints using (SystemHints)
open import Grades.Examples.Time.UpperBound
open import Grades.Examples.Time.Interval

open import Util.Equality

intervals→upper-bounds : interval →ᵍ upper-bound
intervals→upper-bounds = strictᵍ record
  { map          = λ i → [0, max i ]
  ; map-monotone = λ rel → proj₂ rel
  ; map-𝟏        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-ι        = refl
  }

intervals→upper-bounds-grade-system : GradeSystem
intervals→upper-bounds-grade-system = record
  { RGrade = upper-bound
  ; EGrade = interval
  ; ∣-∣ᵉ   = intervals→upper-bounds
  }

-- its hints: an upper endpoint 0 forces the lower one to be 0

intervals→upper-bounds-grade-systemʰ : SystemHints intervals→upper-bounds-grade-system
intervals→upper-bounds-grade-systemʰ = record
  { RHints      = upper-boundʰ
  ; EHints      = intervalʰ
  ; reflects-𝟏? = just (λ _ p → z≤n , p)
  ; witnesses   = λ _ _ _ → []ᴸ
  }
