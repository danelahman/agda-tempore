------------------------------------------------------------------------
-- Worked instance: forgetting the upper bound.                        --
--
-- `IntervalsToLeftSidedIntervals` keeps the lower endpoint alone: the   --
-- effect grade says the uplink takes between 7 and 9 ticks, the         --
-- resource grade only that at least 7 have passed.                      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.IntervalsToLeftSidedIntervals where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (_≤?_)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open _→ᵍ_ using (map; map-monotone)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; eqᵢ; _·ᵢ_; _≾ᵢ_; ↑_; ∞)
  renaming ([_,_] to mkᵢ)

open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

-- every window below has a finite upper endpoint

[_,_] : (m n : ℕ) {m≤n : True (m ≤? n)} → Interval∞
[ m , n ] {m≤n} = mkᵢ m (↑ n) {m≤n}

open import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals
  using (tsi→lsi)

open import Syntax.Grades.Example.Worked.Time.Decide using (≤!)
open import Syntax.Grades.Example.Worked.Time.TwoSided using (uplink-window)

-- the projection reads off the lower endpoint

forget-max : map tsi→lsi uplink-window ≡ [ 7 ,+∞⟩
forget-max = refl

-- so two effect grades differing only in their deadline become the same
-- resource grade: that difference is exactly what is forgotten

deadline-forgotten :
  map tsi→lsi [ 7 , 9 ] ≡ map tsi→lsi [ 7 , 12 ]
deadline-forgotten = refl

-- monotonicity: enlarging the window to `[ 5 , 12 ]` weakens the lower
-- bound to `[ 5 ,+∞⟩`

forget-max-mono : [ 7 ,+∞⟩ ≾ₒ [ 5 ,+∞⟩
forget-max-mono =
  map-monotone tsi→lsi {uplink-window} {[ 5 , 12 ]} (≤! , ≤!)

-- and it is a monoid map: sequencing before or after projecting agrees

forget-max-· : map tsi→lsi ([ 1 , 1 ] ·ᵢ [ 6 , 8 ])
             ≡ map tsi→lsi [ 1 , 1 ] ·ₒ map tsi→lsi [ 6 , 8 ]
forget-max-· = refl
