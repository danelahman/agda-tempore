------------------------------------------------------------------------
-- Programs whose conditions the solver leaves open: the search refutes
-- some at definitions, and the check of a run establishes, refutes or
-- leaves unestablished the others. Exercises retry, the closed check
-- with failing chains and candidates (`Search`, `Entail`, `Localise`,
-- `Solve`).
------------------------------------------------------------------------

module PolymorphicCalculus.Examples.Runs.All where

import PolymorphicCalculus.Examples.Runs

import PolymorphicCalculus.Examples.Runs.Time.RightSided
import PolymorphicCalculus.Examples.Runs.Time.LeftSided
