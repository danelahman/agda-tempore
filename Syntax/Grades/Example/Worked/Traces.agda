------------------------------------------------------------------------
-- Worked instances of the trace grades.                              --
--                                                                    --
-- One module per grade, each worked out twice: as an effect grade,   --
-- along whose order `coerce` moves, and as a resource grade, against --
-- which `unbox` discharges its premise.                              --
--                                                                    --
-- The families differ in what a trace may stand in for. Under        --
-- `Timed.*`, time pays for operations in one direction and           --
-- operations pay for time in the other; under `Subsets.*` neither    --
-- pays for the other, and a grade lists the runs it permits.         --
-- `Regular.*` compares as `Subsets.*` does, over regular sets of     --
-- runs, and is worked out at its order and operations only.          --
--                                                                    --
-- Every run is written out in full in every claim, and every claim   --
-- is established by the decision procedure of the grade.             --
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

-- in dense time: running times with open or closed ends, rational
-- delays, and whole steps read in dense time

import Syntax.Grades.Example.Worked.Traces.Timed.Dense

------------------------------------------------------------------------
-- At the subset order

-- runs that may occur, read disjunctively

import Syntax.Grades.Example.Worked.Traces.Subsets.RightSided

------------------------------------------------------------------------
-- Regular sets

-- canonical tables, and the operations on them

import Syntax.Grades.Example.Worked.Traces.Regular.Base

-- runs that may occur, as a regular set, with literals

import Syntax.Grades.Example.Worked.Traces.Regular.RightSided

------------------------------------------------------------------------
-- Rigid timed regular grades, in whole steps

-- upper bounds: the order of strict waits and budgets, the prototype's
-- tests, the window rule, the delays

import Syntax.Grades.Example.Worked.Traces.Rigid.Regular.RightSided

-- lower bounds: undisturbed waits, explicit flanks

import Syntax.Grades.Example.Worked.Traces.Rigid.Regular.LeftSided
