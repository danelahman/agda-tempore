------------------------------------------------------------------------
-- Worked instances of the grade systems.                              --
--                                                                     --
-- A grade system pairs effect grades -- what a computation may do --   --
-- with resource grades -- what is thereby guaranteed about time -- and --
-- a monoid map `∣_∣ᵉ` projecting the first onto the second. Reading    --
-- the projection tells you what the resource grade may forget.         --
--                                                                     --
-- Each section computes the projection on the sensor node's own grades --
-- and then exercises its monotonicity: an ordering between two effect  --
-- grades must still hold between their images.                        --
--                                                                     --
-- The trace-based systems are parked under `backup/` while the trace   --
-- grades are rebuilt, so only the interval one is worked out here.     --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Systems where

open import Data.Product using (_,_)

open import Util.Equality

open import Syntax.Grades using (_→ᵍ_)

open import Syntax.Grades.Example.Worked.Operations

open _→ᵍ_ using (map; map-monotone)

------------------------------------------------------------------------
-- Forgetting the upper bound
--
-- `IntervalsToLeftSidedIntervals` keeps the lower endpoint alone. The
-- effect grade says the uplink takes between 7 and 9 ticks; the
-- resource grade says only that at least 7 have passed -- which is what
-- a box modality needs, since it is about data having become available,
-- not about a deadline.

open import Syntax.Grades.Example.Time.TwoSided
  using ([_,_,_]; eqᵢ; _·ᵢ_; _≾ᵢ_)

open import Syntax.Grades.Example.Time.LeftSided
  using ([_,+∞⟩; _·ₒ_; _≾ₒ_)

open import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals
  using (tsi→lsi)

open import Syntax.Grades.Example.Worked.Time
  using (≤!; uplink-window)

-- the projection reads off the lower endpoint

forget-max : map tsi→lsi uplink-window ≡ [ 7 ,+∞⟩
forget-max = refl

-- so two effect grades differing only in their deadline become the same
-- resource grade: that difference is exactly what is forgotten

deadline-forgotten :
  map tsi→lsi [ 7 , 9 , ≤! ] ≡ map tsi→lsi [ 7 , 12 , ≤! ]
deadline-forgotten = refl

-- monotonicity: widening the window to `[ 5 , 12 ]` weakens the lower
-- bound to `[ 5 ,+∞⟩`

forget-max-mono : [ 7 ,+∞⟩ ≾ₒ [ 5 ,+∞⟩
forget-max-mono =
  map-monotone tsi→lsi {uplink-window} {[ 5 , 12 , ≤! ]} (≤! , ≤!)

-- and it is a monoid map: sequencing before or after projecting agrees

forget-max-· : map tsi→lsi ([ 1 , 1 , ≤! ] ·ᵢ [ 6 , 8 , ≤! ])
             ≡ map tsi→lsi [ 1 , 1 , ≤! ] ·ₒ map tsi→lsi [ 6 , 8 , ≤! ]
forget-max-· = refl
