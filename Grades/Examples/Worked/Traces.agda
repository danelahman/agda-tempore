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

module Grades.Examples.Worked.Traces where

------------------------------------------------------------------------
-- At the cost-sensitive orders

-- guarantees, at the coverage order

import Grades.Examples.Worked.Traces.Timed.LeftSided

-- allowances, at the allowance order

import Grades.Examples.Worked.Traces.Timed.RightSided

-- and both at once, each endpoint at its own order

import Grades.Examples.Worked.Traces.Timed.TwoSided

-- in dense time: running times with open or closed ends, rational
-- delays, and whole steps read in dense time

import Grades.Examples.Worked.Traces.Timed.Dense

------------------------------------------------------------------------
-- At the subset order

-- runs that may occur, read disjunctively

import Grades.Examples.Worked.Traces.Subsets.RightSided

------------------------------------------------------------------------
-- Regular sets

-- canonical tables, and the operations on them

import Grades.Examples.Worked.Traces.Regular.Base

-- runs that may occur, as a regular set, with literals

import Grades.Examples.Worked.Traces.Regular.RightSided

------------------------------------------------------------------------
-- Rigid timed regular grades, in whole steps

-- upper bounds: the order of strict waits and budgets, the prototype's
-- tests, the window rule, the delays

import Grades.Examples.Worked.Traces.Rigid.Regular.RightSided

-- lower bounds: undisturbed waits, explicit flanks

import Grades.Examples.Worked.Traces.Rigid.Regular.LeftSided

------------------------------------------------------------------------
-- Rigid timed finite-expression grades, in dense time

-- upper bounds: the F4 products at rational lengths, open against
-- closed ends, an equivalence of distinct expressions, the window rule,
-- open running times, the hull

import Grades.Examples.Worked.Traces.Rigid.Finite.RightSided

-- lower bounds: waits add up, undisturbed waits, flanks, open ends, the
-- hull

import Grades.Examples.Worked.Traces.Rigid.Finite.LeftSided

-- intervals: a demanded wait separating budgets, delays read on both
-- sides

import Grades.Examples.Worked.Traces.Rigid.Finite.TwoSided

-- the non-rigid grades as finite-expression grades: the translations,
-- both decisions agreeing, products, a delay read as a budget

import Grades.Examples.Worked.Traces.Rigid.Finite.NonRigid

------------------------------------------------------------------------
-- Rigid timed regular-expression grades, in dense time

-- upper bounds: open bounds adding up, unbounded stretches as
-- iterations, iteration against open ends, the window rule, the plus,
-- the hull

import Grades.Examples.Worked.Traces.Rigid.Rational.RightSided

-- lower bounds: iterated waits, flanks, open ends, the plus, the hull

import Grades.Examples.Worked.Traces.Rigid.Rational.LeftSided

-- intervals: a repeated cycle of work and rest

import Grades.Examples.Worked.Traces.Rigid.Rational.TwoSided

-- comparisons on which the decision and the reference reader of the
-- design study agree

import Grades.Examples.Worked.Traces.Rigid.Rational.CrossChecked
