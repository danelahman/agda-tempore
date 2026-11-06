------------------------------------------------------------------------
-- Worked instances of the grade systems pairing counts with the      --
-- other grades.                                                      --
--                                                                    --
-- An index: one module per system.                                   --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Counts where

-- the finite run set cap, projected onto quotas and onto certain
-- counts

import Grades.Examples.Worked.System.Counts.FiniteRunSets.AtMost
import Grades.Examples.Worked.System.Counts.FiniteRunSets.AtLeast

-- the coverage floor, projected onto certain counts

import Grades.Examples.Worked.System.Counts.Banked.LowerBound

-- the allowance cap does not project onto quotas

import Grades.Examples.Worked.System.Counts.Banked.UpperBound

-- a cost model does not preserve the join

import Grades.Examples.Worked.System.Counts.Time
