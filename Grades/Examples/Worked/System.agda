------------------------------------------------------------------------
-- Worked instances of the grade systems.                             --
--                                                                    --
-- A grade system pairs effect grades (what a computation may do)     --
-- with resource grades (what is thereby guaranteed), with a grade    --
-- algebra morphism `∣-∣ᵉ` from the first to the second; the          --
-- projection determines what the resource grade forgets.             --
--                                                                    --
-- Each module computes the projection on the grades of the sensor    --
-- node and exercises its monotonicity: an ordering between two       --
-- effect grades holds between their images.                          --
--                                                                    --
-- There are two systems from time intervals; ten from trace grades   --
-- to time grades, at the three banked grades, the finite run set     --
-- cap, and the three finite timed regex and three rational timed     --
-- regex grades; one over time lower bounds paired with a lattice;    --
-- and those of the counts. Every projection onto a time grade        --
-- measures a set of runs by a duration; the sets are read            --
-- disjunctively, so a cap measures its slowest member and a floor    --
-- its fastest.                                                       --
--                                                                    --
-- An index: one module per system.                                   --
------------------------------------------------------------------------

module Grades.Examples.Worked.System where

-- forgetting the upper bound of an interval

import Grades.Examples.Worked.System.IntervalsToLowerBounds

-- forgetting the lower bound of an interval

import Grades.Examples.Worked.System.IntervalsToUpperBounds

-- the banked trace grades, measured against the time grades

import Grades.Examples.Worked.System.Traces.Banked.UpperBound
import Grades.Examples.Worked.System.Traces.Banked.LowerBound
import Grades.Examples.Worked.System.Traces.Banked.Interval

-- the finite run set cap, beside the banked floor on the same runs

import Grades.Examples.Worked.System.Traces.FiniteRunSets.UpperBound

-- the finite timed regex grades, measured by their duration hull

import Grades.Examples.Worked.System.Traces.TimedRegex.Finite.UpperBound
import Grades.Examples.Worked.System.Traces.TimedRegex.Finite.LowerBound
import Grades.Examples.Worked.System.Traces.TimedRegex.Finite.Interval

-- the rational timed regex grades, measured by their duration hull

import Grades.Examples.Worked.System.Traces.TimedRegex.Rational.UpperBound
import Grades.Examples.Worked.System.Traces.TimedRegex.Rational.LowerBound
import Grades.Examples.Worked.System.Traces.TimedRegex.Rational.Interval

-- lower bounds on time and a lattice: timed declassification, an
-- embargo alone, and a taint check alone

import Grades.Examples.Worked.System.Product.TimeLowerBoundLattice

-- the trace and interval grades, projected onto counts

import Grades.Examples.Worked.System.Counts
