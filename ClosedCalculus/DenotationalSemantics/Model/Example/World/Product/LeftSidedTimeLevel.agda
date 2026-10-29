------------------------------------------------------------------------
-- A Kripke frame for left-sided time paired with a security level.   --
--                                                                    --
-- A world is a time point and the label reached. A grade             --
-- `([ n ,+∞⟩ , ℓ)` reaches the worlds at least `n` ticks ahead whose --
-- label has risen by at most `ℓ`: the product of the tick frame and  --
-- the label frame.                                                   --
------------------------------------------------------------------------

module ClosedCalculus.DenotationalSemantics.Model.Example.World.Product.LeftSidedTimeLevel where

open import Grades.Examples.SecurityLevel using (LevelLattice; low-high)
open import Grades.Examples.Product.LeftSidedTimeLevel
  using (left-sided-time×level; left-sided-time×low-high)

open import ClosedCalculus.DenotationalSemantics.Model.World
open import ClosedCalculus.DenotationalSemantics.Model.World.Product using (_⊗_)

import ClosedCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSided as LS
open import ClosedCalculus.DenotationalSemantics.Model.Example.World.Labels.SecurityLevel
  using (labels)

-- The frame, at a lattice of levels.

ticks×labels : (L : LevelLattice) → World (left-sided-time×level L)
ticks×labels L = LS.ticks ⊗ labels L

-- at `Low < High`

ticks×low-high : World left-sided-time×low-high
ticks×low-high = ticks×labels low-high
