------------------------------------------------------------------------
-- Worked instances of the grade systems pairing counts with the      --
-- other grades.                                                      --
--                                                                    --
-- An index: one module per system.                                   --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Counts where

-- the finite run set cap, projected onto at-most counts and onto
-- at-least counts

import Grades.Examples.Worked.System.Counts.FiniteRunSets.AtMost
import Grades.Examples.Worked.System.Counts.FiniteRunSets.AtLeast

-- the coverage floor, projected onto at-least counts

import Grades.Examples.Worked.System.Counts.Banked.LowerBound

-- the allowance cap does not project onto at-most counts

import Grades.Examples.Worked.System.Counts.Banked.UpperBound

-- a cost model does not preserve the join

import Grades.Examples.Worked.System.Counts.Time
