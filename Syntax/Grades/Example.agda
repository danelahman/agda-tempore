------------------------------------------------------------------------
-- Example grades, and example grade systems built from them.          --
--                                                                     --
-- A `Grade` (see `Syntax.Grades`) is an ordered monoid with an        --
-- inclusion of ℕ as "so many time steps". A `GradeSystem` is a pair   --
-- of them -- effect grades, recording what a computation may do, and  --
-- resource grades, recording what is thereby guaranteed about time -- --
-- together with a monoid map projecting the first onto the second.    --
--                                                                     --
-- The examples come in two families:                                  --
--                                                                     --
--   * `Time.*`  -- grades that measure only elapsed time, as a bound  --
--     or a window of time steps. Small and self-contained.            --
--                                                                     --
--   * `Traces.*`  -- grades that record *which runs* a computation    --
--     may have had, as a set of timed traces, sharing their carrier   --
--     and monoid (from `Grades.Traces.Sets`) and differing in the     --
--     order they put on it.                                           --
--                                                                     --
-- The trace family is two families of three: `Timed.*` over the       --
-- cost-sensitive orders on traces, and `Subsets.*` over equality,     --
-- each with a floor, a cap and their pairing. A grid over the         --
-- sub-trace orders is parked under `backup/`, imported from nowhere.  --
--                                                                     --
-- Every grade carries its greatest element in its own carrier: for    --
-- the left-sided intervals and the coverage floor that is the unit,   --
-- for the two-sided intervals `[ 0 , ∞ ]`, and the allowance cap and  --
-- the three subset grades each name a point of their own, which is    --
-- then absorbing.                                                     --
--                                                                     --
-- `System.*` pairs them up: each projection says what a resource      --
-- grade may forget about the effect grade it comes from. The two      --
-- subset floors project into extended interval grades, an absorbing   --
-- top having to land on an absorbing top.                             --
--                                                                     --
-- This module is only an index -- the trace-based examples are        --
-- parameterised by the alphabet `Op`, so it lists the pieces rather   --
-- than re-exporting them.                                             --
------------------------------------------------------------------------

module Syntax.Grades.Example where

------------------------------------------------------------------------
-- Time intervals
--
-- Worlds' worth of behaviour compressed to a bound on elapsed time.
-- The one-sided intervals keep one endpoint, the two-sided ones both.

-- "at least `n` time steps"; a smaller bound is the weaker grade

import Syntax.Grades.Example.Time.LeftSided

-- "at most `n` time steps"; the mirror image

import Syntax.Grades.Example.Time.RightSided

-- "between `min` and `max` time steps", with `max` allowed to be `∞`,
-- which imposes no upper bound; a wider window is weaker

import Syntax.Grades.Example.Time.ExtendedNat
import Syntax.Grades.Example.Time.TwoSidedWithInfinity

------------------------------------------------------------------------
-- Sets of timed traces
--
-- A grade records which runs a computation may have had, and the order
-- says what weakening one is allowed to ask for instead. `Traces` is
-- the index.

import Syntax.Grades.Example.Traces

------------------------------------------------------------------------
-- Grade systems
--
-- Each pairs an effect grade with a resource grade, along a projection
-- saying what the resource grade forgets.

-- a grade read as both components, the projection being the identity:
-- nothing is forgotten, and `mapᵉ` drops out of the typing rules

import Syntax.Grades.Example.System.Identity

-- two-sided intervals to left-sided ones: forget the upper bound, keep
-- the guarantee that at least so much time has passed

import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals

-- the timed trace grades to time intervals: forget which runs a grade
-- mentions and which operations they perform, keep what their
-- durations say. The cap keeps the deadline its slowest bound imposes,
-- the floor what its *fastest* guarantee takes -- the set being read
-- disjunctively at both ends -- and the two-sided one is their pair,
-- which lands in an interval at all because the coherence field puts
-- the fastest guarantee below the slowest allowance

import Syntax.Grades.Example.System.Traces.Timed.RightSided
import Syntax.Grades.Example.System.Traces.Timed.LeftSided
import Syntax.Grades.Example.System.Traces.Timed.TwoSided

-- the subset grades to time intervals: the same, except that every
-- endpoint is measured by its *slowest* member. Above for the usual
-- reason, below because that floor is read conjunctively -- so the
-- aggregation follows how a set is read, not which side it bounds

import Syntax.Grades.Example.System.Traces.Subsets.RightSided
import Syntax.Grades.Example.System.Traces.Subsets.LeftSided
import Syntax.Grades.Example.System.Traces.Subsets.TwoSided

------------------------------------------------------------------------
-- Worked instances
--
-- All of the above at one fixed alphabet, with the orderings that hold
-- between concrete grades and the effect of each morphism on them
-- exhibited as checked terms, and example computations typed against
-- the grades. A reader's tour of this whole subtree.

import Syntax.Grades.Example.Worked
