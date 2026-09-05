------------------------------------------------------------------------
-- Example grades, and example grade systems built from them.          --
--                                                                     --
-- A `Grade` (see `Syntax.Grades`) is an ordered monoid with an         --
-- inclusion of ℕ as "so many time steps". A `GradeSystem` is a pair    --
-- of them -- effect grades, recording what a computation may do, and   --
-- resource grades, recording what is thereby guaranteed about time --   --
-- together with a monoid map projecting the first onto the second.     --
--                                                                     --
-- The examples come in two families:                                   --
--                                                                     --
--   * `Interval.*`  -- grades that measure only elapsed time, as a     --
--     bound or a window of time steps. Small and self-contained.       --
--                                                                     --
--   * `TraceSet.*`  -- grades that record *which runs* a computation   --
--     may have, as a set of timed traces. All three share their        --
--     carrier and monoid (from `Grades.Traces.Sets`) and differ only   --
--     in the order they put on it, from coarsest to finest.            --
--                                                                     --
-- `System.*` then pairs them up. Reading the projections tells the     --
-- story of the development: each one says what a resource grade is     --
-- allowed to forget about the effect grade it comes from.              --
--                                                                     --
-- This module is only an index -- the trace-based examples are         --
-- parameterised by the alphabet `Op`, so it lists the pieces rather    --
-- than re-exporting them.                                              --
------------------------------------------------------------------------

module Syntax.Grades.Example where

------------------------------------------------------------------------
-- Time intervals
--
-- Worlds' worth of behaviour compressed to a bound on elapsed time.
-- The one-sided intervals keep one endpoint, the two-sided ones both.

-- "at least `n` time steps"; a smaller bound is the weaker grade

import Syntax.Grades.Example.Interval.LeftSided

-- "at most `n` time steps"; the mirror image

import Syntax.Grades.Example.Interval.RightSided

-- "between `min` and `max` time steps"; a wider window is weaker

import Syntax.Grades.Example.Interval.TwoSided

-- the same, with `max` allowed to be `∞`, which imposes no upper bound

import Syntax.Grades.Example.Interval.ExtendedNat
import Syntax.Grades.Example.Interval.TwoSidedWithInfinity

------------------------------------------------------------------------
-- Sets of timed traces
--
-- One carrier, three orders. Each order says what weakening a grade is
-- allowed to add, and so how much a computation may deviate from the
-- schedule its grade prescribes.

-- ordered by inclusion: weakening only adds runs, and the operations
-- need no execution times at all

import Syntax.Grades.Example.TraceSet.Inclusion

-- ordered by the Hoare lift of the sub-trace preorder: a run may also
-- shrink to anything that fits inside a schedule already present

import Syntax.Grades.Example.TraceSet.UpToSubtrace

-- ordered by the convex (Egli-Milner) lift: shrinking is allowed only
-- between runs already present, so the extremes stay exact

import Syntax.Grades.Example.TraceSet.Convex

------------------------------------------------------------------------
-- Grade systems
--
-- Each pairs an effect grade with a resource grade, along a projection
-- saying what the resource grade forgets.

-- two-sided intervals to left-sided ones: forget the upper bound, keep
-- the guarantee that at least so much time has passed

import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals

-- sets of traces to sets of traces over a sub-alphabet: forget the
-- operations that are not being accounted for

import Syntax.Grades.Example.System.TracesToRestrictedTraces

-- sets of traces to time intervals: forget which runs there were, keep
-- the window between their best-case and worst-case durations

import Syntax.Grades.Example.System.TracesToTimeIntervals

-- sets of traces to the same sets read against a cost model: forget
-- nothing, but compare the runs up to what fits inside a schedule

import Syntax.Grades.Example.System.TracesToCostAwareTraces
