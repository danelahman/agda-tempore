------------------------------------------------------------------------
-- A Kripke frame for lower bounds on time paired with a lattice.     --
--                                                                    --
-- A world is a time point and the label reached. A grade             --
-- `([ n ,+∞⟩ , ℓ)` reaches the worlds at least `n` ticks ahead whose --
-- label has risen by at most `ℓ`: the product of the tick frame and  --
-- the label frame.                                                   --
------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Product.TimeLowerBoundLattice where

open import Grades.Examples.Lattice using (LevelLattice; low-high)
open import Grades.Examples.Product.TimeLowerBoundLattice
  using (time-lower-bound×lattice; time-lower-bound×low-high)

open import MonomorphicCalculus.DenotationalSemantics.Model.World
open import MonomorphicCalculus.DenotationalSemantics.Model.World.Product using (_⊗_)

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.LowerBound as LS
open import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Labels.Lattice
  using (labels)

-- The frame, at a lattice of levels.

ticks×labels : (L : LevelLattice) → World (time-lower-bound×lattice L)
ticks×labels L = LS.ticks ⊗ labels L

-- at `Low < High`

ticks×low-high : World time-lower-bound×low-high
ticks×low-high = ticks×labels low-high
