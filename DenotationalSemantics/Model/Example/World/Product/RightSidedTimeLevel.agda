------------------------------------------------------------------------
-- A Kripke frame for right-sided time paired with a security level.   --
--                                                                     --
-- A world is a time point and the label reached. A grade              --
-- `([0, n ] , ℓ)` reaches the worlds at most `n` ticks ahead whose    --
-- label has risen by at most `ℓ`: the product of the tick frame,      --
-- restricted to forward moves, and the label frame.                   --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World.Product.RightSidedTimeLevel where

open import Data.Nat.Base using (_≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-irrelevant)

open import Syntax.Grades.Example.Time.RightSided using (right-sided-intervals)
open import Syntax.Grades.Example.SecurityLevel using (LevelLattice; low-high)
open import Syntax.Grades.Example.Product.RightSidedTimeLevel
  using (right-sided-time×level; right-sided-time×low-high)

open import DenotationalSemantics.Model.World
open import DenotationalSemantics.Model.World.Product using (_⊗_)
open import DenotationalSemantics.Model.World.Action using (forward)

import DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided as RS
open import DenotationalSemantics.Model.Example.World.Labels.SecurityLevel
  using (labels)

-- time: the right-sided tick frame, forward moves only

time : World right-sided-intervals
time = forward RS.ticks _≤_ ≤-refl ≤-trans ≤-irrelevant

-- The frame, at a lattice of levels.

ticks×labels : (L : LevelLattice) → World (right-sided-time×level L)
ticks×labels L = time ⊗ labels L

-- at `Low < High`

ticks×low-high : World right-sided-time×low-high
ticks×low-high = ticks×labels low-high
