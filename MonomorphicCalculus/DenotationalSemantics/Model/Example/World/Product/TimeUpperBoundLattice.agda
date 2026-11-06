------------------------------------------------------------------------
-- A Kripke frame for upper bounds on time paired with a lattice.     --
--                                                                    --
-- A world is a time point and the label reached. A grade             --
-- `([0, n ] , ℓ)` reaches the worlds at most `n` ticks ahead whose   --
-- label has risen by at most `ℓ`: the product of the tick frame and  --
-- the label frame, both moving only forward.                         --
------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Product.TimeUpperBoundLattice where

open import Grades.Examples.Lattice using (LevelLattice; low-high)
open import Grades.Examples.Product.TimeUpperBoundLattice
  using (time-upper-bound×lattice; time-upper-bound×low-high)

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Product using (_⊗_)

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.UpperBound as RS
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Labels.Lattice
  using (labels)

-- The frame, at a lattice of levels.

ticks×labels : (L : LevelLattice) → World (time-upper-bound×lattice L)
ticks×labels L = RS.ticks ⊗ labels L

-- at `Low < High`

ticks×low-high : World time-upper-bound×low-high
ticks×low-high = ticks×labels low-high
