------------------------------------------------------------------------
-- Worked instances of the trace grades.                               --
--                                                                     --
-- One module per grade, each worked out twice over: once as an effect  --
-- grade, where `coerce` moves along the order, and once as a resource  --
-- grade, where `unbox` discharges its premise against it.              --
--                                                                     --
-- Read the two families side by side and the difference is in what     --
-- one trace may do for another. `Timed.*` lets time pay for work in    --
-- one direction and work pay for time in the other; `Subsets.*` lets   --
-- nothing pay for anything, so a grade has to list what it means.      --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure, so the tables  --
-- are checked rather than annotated.                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces where

------------------------------------------------------------------------
-- At the cost-sensitive orders

-- guarantees, at the coverage order

import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided

-- allowances, at the allowance order

import Syntax.Grades.Example.Worked.Traces.Timed.RightSided

-- and both at once, each endpoint at its own order

import Syntax.Grades.Example.Worked.Traces.Timed.TwoSided

------------------------------------------------------------------------
-- At the subset order

-- runs that must remain reachable, read conjunctively

import Syntax.Grades.Example.Worked.Traces.Subsets.LeftSided

-- runs that may occur, read disjunctively

import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided

-- and both at once, as an interval in the subset lattice

import Syntax.Grades.Example.Worked.Traces.Subsets.TwoSided
