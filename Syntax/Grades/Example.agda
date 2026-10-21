------------------------------------------------------------------------
-- Example grades, and example grade systems built from them.         --
--                                                                    --
-- A `Grade` (see `Syntax.Grades`) is a partially ordered monoid with --
-- binary joins, a greatest element, and a monoid morphism `of-dur`   --
-- from a monoid of durations; here the durations are ℕ, read as a    --
-- number of time steps. A `GradeSystem` consists of two grades       --
-- (effect grades, recording what a computation may do, and resource  --
-- grades, recording what is thereby guaranteed about time) and a     --
-- grade morphism from the first to the second.                       --
--                                                                    --
-- The examples form four families:                                   --
--                                                                    --
--   * `Time.*`: grades that measure elapsed time only, as a bound or --
--     a window of time steps, over ℕ or, in `Time.Dense.*`, over the --
--     non-negative rationals ℚ≥0; morphisms embed the discrete       --
--     grades in the dense ones.                                      --
--                                                                    --
--   * `Traces.*`: grades that record *which runs* a computation may  --
--     have had, as a set of timed traces, differing in the order on  --
--     the sets.                                                      --
--                                                                    --
--   * `Counts.*`: grades that count, per operation (or per class of  --
--     operations, under an index into `Fin n`), how often a          --
--     computation draws on each; `AtMost`/`AtLeast` are quotas and   --
--     guarantees, and `Power` is the generic `n`-counter product.    --
--                                                                    --
--   * `SecurityLevel`: a decidable join-semilattice of levels,       --
--     floating upward as data is touched; instances are the          --
--     two-point `Low < High` and taint sets over `Fin n`.            --
--                                                                    --
-- `Product.*` pairs members of these families by the product of      --
-- grades of `Syntax.Grades.Product`: left- and right-sided time with --
-- a security level, and right-sided time with an energy budget       --
-- (right-sided time read as expenditure rather than elapsed time).   --
--                                                                    --
-- The trace family has three parts: `Timed.*` over the               --
-- cost-sensitive orders on traces, with a floor, a cap and their     --
-- pairing; `Subsets.*` over equality, with a cap; and `Regular.*`, a --
-- cap at inclusion over regular sets.                                --
--                                                                    --
-- `System.*` assembles grade systems; each projection determines     --
-- what a resource grade forgets about the effect grade it comes      --
-- from.                                                              --
--                                                                    --
-- The module is an index: the trace-based examples are parameterised --
-- by the alphabet `Op`, and are listed rather than re-exported.      --
------------------------------------------------------------------------

module Syntax.Grades.Example where

------------------------------------------------------------------------
-- Time intervals
--
-- Bounds on elapsed time. The one-sided intervals have one endpoint,
-- the two-sided ones two.

-- "at least `n` time steps"; a smaller bound is the weaker grade

import Syntax.Grades.Example.Time.LeftSided

-- "at most `n` time steps"; the mirror image

import Syntax.Grades.Example.Time.RightSided

-- "between `min` and `max` time steps", with `max` allowed to be `∞`,
-- which imposes no upper bound; a wider window is weaker

import Syntax.Grades.Example.Time.ExtendedNat
import Syntax.Grades.Example.Time.TwoSidedWithInfinity

-- intervals of any time domain, each end open or closed, the upper
-- one possibly absent

import Syntax.Grades.Example.Time.Intervals

-- the same three shapes over the non-negative rationals ℚ≥0, with
-- morphisms embedding the discrete grades above; the two-sided grade
-- has open or closed ends, the closed intervals being a sub-grade

import Syntax.Grades.Example.Time.Dense.NonNegativeRational
import Syntax.Grades.Example.Time.Dense.ExtendedRational
import Syntax.Grades.Example.Time.Dense.LeftSided
import Syntax.Grades.Example.Time.Dense.RightSided
import Syntax.Grades.Example.Time.Dense.TwoSidedClosed
import Syntax.Grades.Example.Time.Dense.TwoSided

------------------------------------------------------------------------
-- Security levels
--
-- A decidable join-semilattice of levels, floating upward on read.

import Syntax.Grades.Example.SecurityLevel

------------------------------------------------------------------------
-- Products
--
-- `Syntax.Grades.Product` pairs two grades componentwise; these pair
-- members of the families above.

-- left-sided time and a security level: an embargo with a taint check

import Syntax.Grades.Example.Product.LeftSidedTimeLevel

-- right-sided time and a security level: an expiring, untainted
-- capability

import Syntax.Grades.Example.Product.RightSidedTimeLevel

-- right-sided time and an energy budget: a calibration that drifts
-- with both

import Syntax.Grades.Example.Product.RightSidedTimeEnergy

------------------------------------------------------------------------
-- Sets of timed traces
--
-- A grade records which runs a computation may have had, and the order
-- determines the weakenings of a grade. `Traces` is the index.

import Syntax.Grades.Example.Traces

------------------------------------------------------------------------
-- Per-operation counts
--
-- A grade is one bound per counter, `n` counters for an alphabet with
-- `n` operations, or classes of them under a coarser index into
-- `Fin n`.

-- the power of a grade: `n` counters, each graded by `G`

import Syntax.Grades.Example.Counts.Power

-- "at most `k` of each operation"; a quota, the pointwise maximum its
-- join

import Syntax.Grades.Example.Counts.AtMost

-- "at least `k` of each operation"; a guarantee, the pointwise
-- minimum its join

import Syntax.Grades.Example.Counts.AtLeast

-- the greatest and least value of a natural-number measure over a
-- non-empty list, the toolkit the extremal counts are built from

import Syntax.Grades.Example.Counts.Extrema

-- how often a timed trace draws on each counter

import Syntax.Grades.Example.Counts.Occurrences

------------------------------------------------------------------------
-- Grade systems
--
-- Each pairs an effect grade with a resource grade, along a projection
-- saying what the resource grade forgets.

-- a grade read as both components, the projection being the identity:
-- nothing is forgotten, and `mapᵉ` drops out of the typing rules

import Syntax.Grades.Example.System.Identity

-- left-sided time paired with a security level, at the identity, at
-- time alone, and at the level alone: timed declassification and its
-- two projections, an embargo alone and a taint check alone

import Syntax.Grades.Example.System.Product.LeftSidedTimeLevel

-- two-sided intervals to left-sided ones: forget the upper bound, keep
-- the guarantee that at least so much time has passed

import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals

-- the timed trace grades to time intervals: forget which runs a grade
-- mentions and which operations they perform, keep what their
-- durations say -- the cap the deadline its slowest bound imposes, the
-- floor what its *fastest* guarantee takes, and the two-sided one
-- their pair

import Syntax.Grades.Example.System.Traces.Timed.RightSided
import Syntax.Grades.Example.System.Traces.Timed.LeftSided
import Syntax.Grades.Example.System.Traces.Timed.TwoSided

-- the subset cap to time intervals: the same, the deadline being the
-- one its *slowest* listed run imposes

import Syntax.Grades.Example.System.Traces.Subsets.RightSided

-- the rigid finite-expression grades to time intervals by their
-- duration hull: an upper bound to the longest run it admits, a lower
-- bound to the shortest, an interval to the pair of its ends

import Syntax.Grades.Example.System.Traces.Rigid.Finite.RightSided
import Syntax.Grades.Example.System.Traces.Rigid.Finite.LeftSided
import Syntax.Grades.Example.System.Traces.Rigid.Finite.TwoSided

-- the same for the rigid regular-expression grades, iteration included

import Syntax.Grades.Example.System.Traces.Rigid.Rational.RightSided
import Syntax.Grades.Example.System.Traces.Rigid.Rational.LeftSided
import Syntax.Grades.Example.System.Traces.Rigid.Rational.TwoSided

-- the subset cap to at-most counts: on each counter, the greatest
-- count among the listed traces -- a quota that covers the run that
-- draws on it most

import Syntax.Grades.Example.System.Counts.Subsets.AtMost

-- the subset cap to at-least counts: on each counter, the least count
-- among the listed traces -- a guarantee certain of every run

import Syntax.Grades.Example.System.Counts.Subsets.AtLeast

-- antichains of guarantees to at-least counts, at an arbitrary trace
-- order that never covers a demand with fewer operations; instantiated
-- at the coverage floor

import Syntax.Grades.Example.System.Counts.Lifted.LeftSided
import Syntax.Grades.Example.System.Counts.Timed.LeftSided

-- the allowance cap does not project onto quotas: no morphism into
-- at-most counts counts what a bound permits

import Syntax.Grades.Example.System.Counts.Timed.RightSided

-- no count grade projects onto time, and a cost model preserves all
-- but the join when time is paired with the counts

import Syntax.Grades.Example.System.Counts.Time

-- upper bounds on counts by name, an indexed grade; flow-sensitive
-- levels and windowed schedules, semidirect products

import Syntax.Grades.Example.Counts.UpperBound
import Syntax.Grades.Example.SemiDirect.FlowLevels
import Syntax.Grades.Example.SemiDirect.WindowedSchedules

-- the levels each resource reaches: a trough, a range of net changes
-- and a peak, over the integers with infinities

import Syntax.Grades.Example.SemiDirect.ExtendedInteger
import Syntax.Grades.Example.SemiDirect.ResourceLevels

-- the costs of switching between the modes of a device, as max-plus
-- mode matrices

import Syntax.Grades.Example.SemiDirect.ModeSwitchCosts

-- the time spent in each mode of a device, as mode matrices of
-- realisable boxes of intervals

import Syntax.Grades.Example.SemiDirect.ModeTimes.Boxes
import Syntax.Grades.Example.SemiDirect.ModeTimes

------------------------------------------------------------------------
-- Worked instances
--
-- All of the above at one alphabet: the orderings between concrete
-- grades and the action of each morphism on them, as checked terms, and
-- example computations typed at the grades.

import Syntax.Grades.Example.Worked
