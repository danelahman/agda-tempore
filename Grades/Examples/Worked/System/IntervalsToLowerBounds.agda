------------------------------------------------------------------------
-- Worked instance: forgetting the upper bound.                       --
--                                                                    --
-- `IntervalsToLowerBounds` keeps the lower endpoint only: the        --
-- effect grade states that the uplink takes between 7 and 9 ticks,   --
-- the resource grade only that at least 7 have passed.               --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.IntervalsToLowerBounds where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.Interval
  using (Interval∞; eqᵢ; _·ᵢ_; _≾ᵢ_; ↑_; ∞)
  renaming ([_,_] to mkᵢ)

open import Grades.Examples.Time.LowerBound
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

-- every window below has a finite upper endpoint

[_,_] : (m n : ℕ) {m≤n : True (m ≤? n)} → Interval∞
[ m , n ] {m≤n} = mkᵢ m (↑ n) {m≤n}

open import Grades.Examples.System.IntervalsToLowerBounds
  using (intervals→lower-bounds)

open import Grades.Examples.Worked.Time.Decide using (≤!)
open import Grades.Examples.Worked.Time.Interval using (uplink-window)

-- the projection reads off the lower endpoint

forget-max : map intervals→lower-bounds uplink-window ≡ [ 7 ,+∞⟩
forget-max = refl

-- so two effect grades differing only in their deadline become the same
-- resource grade: that difference is exactly what is forgotten

deadline-forgotten :
  map intervals→lower-bounds [ 7 , 9 ] ≡ map intervals→lower-bounds [ 7 , 12 ]
deadline-forgotten = refl

-- monotonicity: enlarging the window to `[ 5 , 12 ]` weakens the lower
-- bound to `[ 5 ,+∞⟩`

forget-max-mono : [ 7 ,+∞⟩ ≾ₒ [ 5 ,+∞⟩
forget-max-mono =
  map-monotone intervals→lower-bounds {uplink-window} {[ 5 , 12 ]} (≤! , ≤!)

-- and it is a monoid map: sequencing before or after projecting agrees

forget-max-· : map intervals→lower-bounds ([ 1 , 1 ] ·ᵢ [ 6 , 8 ])
             ≡ map intervals→lower-bounds [ 1 , 1 ] ·ₒ map intervals→lower-bounds [ 6 , 8 ]
forget-max-· = refl
