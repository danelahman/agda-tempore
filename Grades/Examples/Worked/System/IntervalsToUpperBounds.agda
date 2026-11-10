------------------------------------------------------------------------
-- Worked instance: forgetting the lower bound.                       --
--                                                                    --
-- `IntervalsToUpperBounds` keeps the upper endpoint only: the        --
-- effect grade states that the uplink takes between 7 and 9 ticks,   --
-- the resource grade only that at most 9 have passed.                --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.IntervalsToUpperBounds where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)

open _→ᵍ_ using (map; map-monotone)

open import Grades.Examples.Time.Interval
  using (Interval∞; _·ᵢ_; ↑_)
  renaming ([_,_] to mkᵢ)

open import Grades.Examples.Time.UpperBound
  using ([0,_]; _·ₒ_; _≾ₒ_)

-- every window below has a finite upper endpoint

[_,_] : (m n : ℕ) {m≤n : True (m ≤? n)} → Interval∞
[ m , n ] {m≤n} = mkᵢ m (↑ n) {m≤n}

open import Grades.Examples.System.IntervalsToUpperBounds
  using (intervals→upper-bounds)

open import Grades.Examples.Worked.Time.Decide using (≤!)
open import Grades.Examples.Worked.Time.Interval using (uplink-window)

-- the projection reads off the upper endpoint

forget-min : map intervals→upper-bounds uplink-window ≡ [0, ↑ 9 ]
forget-min = refl

-- so two effect grades differing only in their earliest completion
-- become the same resource grade

earliest-forgotten :
  map intervals→upper-bounds [ 7 , 9 ] ≡ map intervals→upper-bounds [ 2 , 9 ]
earliest-forgotten = refl

-- monotonicity: enlarging the window to `[ 5 , 12 ]` weakens the upper
-- bound to `[0, ↑ 12 ]`

forget-min-mono : [0, ↑ 9 ] ≾ₒ [0, ↑ 12 ]
forget-min-mono =
  map-monotone intervals→upper-bounds {uplink-window} {[ 5 , 12 ]} (≤! , ≤!)

-- and it is a monoid map: sequencing before or after projecting agrees

forget-min-· : map intervals→upper-bounds ([ 1 , 1 ] ·ᵢ [ 6 , 8 ])
             ≡ map intervals→upper-bounds [ 1 , 1 ] ·ₒ map intervals→upper-bounds [ 6 , 8 ]
forget-min-· = refl
