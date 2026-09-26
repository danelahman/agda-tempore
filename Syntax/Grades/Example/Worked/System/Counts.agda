------------------------------------------------------------------------
-- Worked instances of the grade systems pairing counts with the      --
-- other grades.                                                      --
--                                                                    --
-- An index: one module per system.                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System.Counts where

-- the subset cap, projected onto quotas and onto certain counts

import Syntax.Grades.Example.Worked.System.Counts.Subsets.AtMost
import Syntax.Grades.Example.Worked.System.Counts.Subsets.AtLeast

-- the coverage floor, projected onto certain counts

import Syntax.Grades.Example.Worked.System.Counts.Timed.LeftSided

-- the allowance cap does not project onto quotas

import Syntax.Grades.Example.Worked.System.Counts.Timed.RightSided

-- a cost model does not preserve the join

import Syntax.Grades.Example.Worked.System.Counts.Time
