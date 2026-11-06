------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                  --
--                                                                    --
-- A grade records the runs a computation may have. The families      --
-- differ in the comparison between a run and a listed trace:         --
--                                                                    --
--   Banked.*          the two cost-sensitive orders on traces. Going --
--                    up the allowance order, an operation becomes a  --
--                    delay that covers it; going up the coverage     --
--                    order, a run may do more than is demanded.      --
--                                                                    --
--   FiniteRunSets.*  equality: a run is a listed trace or it is      --
--                    not, and the lift is subset inclusion.          --
--                                                                    --
-- `Banked.*` has a floor, a cap and their pairing:                   --
--                                                                    --
--   Banked.LowerBound   a lower bound on what happened, reduced to   --
--                     the antichain of its weakest guarantees        --
--   Banked.UpperBound  an upper bound, reduced to the antichain of   --
--                     its most permissive bounds                     --
--   Banked.Interval    both at once, with a coherence field          --
--                                                                    --
-- `FiniteRunSets.*` has the cap, `FiniteRunSets.UpperBound`.         --
--                                                                    --
-- `Regular.*` has the cap at inclusion, over regular sets of runs    --
-- represented by canonical minimal automata.                         --
--                                                                    --
-- Every endpoint is read disjunctively, one listed trace carrying    --
-- the grade: grades weaken by gaining members, and the union of two  --
-- grades is their join.                                              --
--                                                                    --
-- The `Banked.*` grades are `Traces.Lifted.*` instantiated at a      --
-- trace order; the `FiniteRunSets.*` grade is built directly on the  --
-- order `_⊑_` of `Sets`, the discrete order not being a `TraceOrder` --
-- (it lacks `≼-nil`).                                                --
------------------------------------------------------------------------

module Grades.Examples.Traces where

------------------------------------------------------------------------
-- The constructions, over an arbitrary order (or pair of orders)

import Grades.Examples.Traces.Lifted.LowerBound
import Grades.Examples.Traces.Lifted.UpperBound
import Grades.Examples.Traces.Lifted.Interval

-- grade morphisms between them along a map of traces between two time
-- domains

import Grades.Examples.Traces.Lifted.Morphism

------------------------------------------------------------------------
-- At the cost-sensitive orders
--
-- The floor takes the coverage order, in which time never covers an
-- operation, and the cap the allowance order, in which a listed delay
-- is a budget that pays for operations.

import Grades.Examples.Traces.Banked.LowerBound
import Grades.Examples.Traces.Banked.UpperBound
import Grades.Examples.Traces.Banked.Interval

-- as interval-letter grades of `Grades.Exact`: the orders preserved and
-- reflected, products and joins kept

import Grades.Examples.Traces.Banked.ExactGrades

-- along a morphism of time domains, and whole steps read in dense time

import Grades.Examples.Traces.Banked.Morphism
import Grades.Examples.Traces.Banked.Rational

------------------------------------------------------------------------
-- Finite run sets, at the subset order
--
-- The comparison is equality, and the cap is subset inclusion `X ⊆ Q`:
-- every run a computation may have is one of the listed traces.

import Grades.Examples.Traces.FiniteRunSets.Base
import Grades.Examples.Traces.FiniteRunSets.UpperBound

------------------------------------------------------------------------
-- Regular trace languages
--
-- A grade is a non-empty regular set of runs, represented by the
-- canonical minimal automaton of its encoding over `Op ⊎ tick`; the
-- finite run sets of `FiniteRunSets.UpperBound` embed in it, but no
-- grade morphism exists.

import Grades.Examples.Traces.Regular.UpperBound
import Grades.Examples.Traces.Regular.FiniteRunSets

------------------------------------------------------------------------
-- Rigid timed regex grades, in whole steps
--
-- A grade is a non-empty regular language of whole-step slots closed
-- downward under the slot order, the order on exact words
-- (`Grades.Exact`) read slot by slot. Literals are one-sided
-- expressions over interval letters; upper bounds, lower bounds, and
-- their pairs.

import Grades.Examples.Traces.TimedRegex.Nat.Base
import Grades.Examples.Traces.TimedRegex.Nat.UpperBound
import Grades.Examples.Traces.TimedRegex.Nat.LowerBound
import Grades.Examples.Traces.TimedRegex.Nat.Interval

------------------------------------------------------------------------
-- Rigid timed finite-expression grades
--
-- Grades over the non-negative rationals: finite one-sided
-- expressions over interval letters with open or closed ends, compared
-- by the runs they denote and decided by the pouring reader
-- (`Grades.Exact.Finite`); upper bounds, lower bounds, and their pairs.

import Grades.Examples.Traces.TimedRegex.Finite.Base
import Grades.Examples.Traces.TimedRegex.Finite.UpperBound
import Grades.Examples.Traces.TimedRegex.Finite.LowerBound
import Grades.Examples.Traces.TimedRegex.Finite.Interval

-- the non-rigid banked trace grades read as finite-expression grades

import Grades.Examples.Traces.TimedRegex.Finite.NonRigid

------------------------------------------------------------------------
-- Rigid timed regex grades
--
-- Grades over the non-negative rationals: one-sided expressions with
-- iteration over interval letters, compared by the runs they denote and
-- decided by the automaton of the reader over a common unit
-- (`Grades.Exact.Regular`); upper bounds, lower bounds, and their pairs.

import Grades.Examples.Traces.TimedRegex.Rational.Base
import Grades.Examples.Traces.TimedRegex.Rational.UpperBound
import Grades.Examples.Traces.TimedRegex.Rational.LowerBound
import Grades.Examples.Traces.TimedRegex.Rational.Interval
