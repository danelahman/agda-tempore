------------------------------------------------------------------------
-- The concrete grade algebras and grade systems. The modules over an
-- operation alphabet are parameterised by it and listed, not opened.
------------------------------------------------------------------------

module Grades.Examples where

------------------------------------------------------------------------
-- Time intervals
--
-- Bounds on elapsed time. The one-sided intervals have one endpoint,
-- the two-sided ones two.

-- "at least `n` time steps"; a smaller bound is the weaker grade

import Grades.Examples.Time.LeftSided

-- "at most `n` time steps"; the mirror image

import Grades.Examples.Time.RightSided

-- "between `min` and `max` time steps", with `max` allowed to be `∞`,
-- which imposes no upper bound; a wider window is weaker

import Grades.Examples.Time.ExtendedNat
import Grades.Examples.Time.TwoSidedWithInfinity

-- intervals of any time domain, each end open or closed, the upper
-- one possibly absent

import Grades.Examples.Time.Intervals

-- the same three shapes over the non-negative rationals ℚ≥0, with
-- morphisms embedding the discrete grades above; the two-sided grade
-- and the one-sided `*Cut` grades have open or closed ends, the closed
-- intervals being sub-grades, and the two-sided intervals map onto
-- each of their ends

import Grades.Examples.Time.Dense.ExtendedRational
import Grades.Examples.Time.Dense.LeftSided
import Grades.Examples.Time.Dense.RightSided
import Grades.Examples.Time.Dense.TwoSidedClosed
import Grades.Examples.Time.Dense.TwoSided
import Grades.Examples.Time.Dense.LeftSidedCut
import Grades.Examples.Time.Dense.RightSidedCut

------------------------------------------------------------------------
-- Security levels
--
-- A decidable join-semilattice of levels, floating upward on read.

import Grades.Examples.SecurityLevel

------------------------------------------------------------------------
-- Products
--
-- `Grades.Product` pairs two grades componentwise; these pair
-- members of the families above.

-- left-sided time and a security level: an embargo with a taint check

import Grades.Examples.Product.LeftSidedTimeLevel

-- right-sided time and a security level: an expiring, untainted
-- capability

import Grades.Examples.Product.RightSidedTimeLevel

-- right-sided time and an energy budget: a calibration that drifts
-- with both

import Grades.Examples.Product.RightSidedTimeEnergy

------------------------------------------------------------------------
-- Sets of timed traces
--
-- A grade records which runs a computation may have had, and the order
-- determines the weakenings of a grade. `Traces` is the index.

import Grades.Examples.Traces

------------------------------------------------------------------------
-- Per-operation counts
--
-- A grade is one bound per counter, `n` counters for an alphabet with
-- `n` operations, or classes of them under a coarser index into
-- `Fin n`.

-- the power of a grade: `n` counters, each graded by `G`

import Grades.Examples.Counts.Power

-- "at most `k` of each operation"; a quota, the pointwise maximum its
-- join

import Grades.Examples.Counts.AtMost

-- "at least `k` of each operation"; a guarantee, the pointwise
-- minimum its join

import Grades.Examples.Counts.AtLeast

-- the greatest and least value of a natural-number measure over a
-- non-empty list, the toolkit the extremal counts are built from

import Grades.Examples.Counts.Extrema

-- how often a timed trace draws on each counter

import Grades.Examples.Counts.Occurrences

------------------------------------------------------------------------
-- Grade systems
--
-- Each pairs an effect grade with a resource grade, along a projection
-- saying what the resource grade forgets.

-- a grade read as both components, the projection being the identity:
-- nothing is forgotten, and `∣_∣ᵉ` drops out of the typing rules

import Grades.Examples.System.Identity

-- left-sided time paired with a security level, at the identity, at
-- time alone, and at the level alone: timed declassification and its
-- two projections, an embargo alone and a taint check alone

import Grades.Examples.System.Product.LeftSidedTimeLevel

-- two-sided intervals to left-sided ones: forget the upper bound, keep
-- the guarantee that at least so much time has passed

import Grades.Examples.System.IntervalsToLeftSidedIntervals

-- the timed trace grades to time intervals: forget which runs a grade
-- mentions and which operations they perform, keep what their
-- durations say: the cap the deadline its slowest bound imposes, the
-- floor what its fastest guarantee takes, and the two-sided one their
-- pair

import Grades.Examples.System.Traces.Timed.RightSided
import Grades.Examples.System.Traces.Timed.LeftSided
import Grades.Examples.System.Traces.Timed.TwoSided

-- the subset cap to time intervals: the same, the deadline being the
-- one its slowest listed run imposes

import Grades.Examples.System.Traces.Subsets.RightSided

-- the rigid finite-expression grades to time intervals by their
-- duration hull: an upper bound to the longest run it admits, a lower
-- bound to the shortest, an interval to the pair of its ends

import Grades.Examples.System.Traces.Rigid.Finite.RightSided
import Grades.Examples.System.Traces.Rigid.Finite.LeftSided
import Grades.Examples.System.Traces.Rigid.Finite.TwoSided

-- the same for the rigid regular-expression grades, iteration included

import Grades.Examples.System.Traces.Rigid.Rational.RightSided
import Grades.Examples.System.Traces.Rigid.Rational.LeftSided
import Grades.Examples.System.Traces.Rigid.Rational.TwoSided

-- the subset cap to at-most counts: on each counter, the greatest
-- count among the listed traces, a quota covering the run that draws
-- on it most

import Grades.Examples.System.Counts.Subsets.AtMost

-- the subset cap to at-least counts: on each counter, the least count
-- among the listed traces, a guarantee certain of every run

import Grades.Examples.System.Counts.Subsets.AtLeast

-- antichains of guarantees to at-least counts, at an arbitrary trace
-- order that never covers a demand with fewer operations; instantiated
-- at the coverage floor

import Grades.Examples.System.Counts.Lifted.LeftSided
import Grades.Examples.System.Counts.Timed.LeftSided

-- the allowance cap does not project onto quotas: no morphism into
-- at-most counts counts what a bound permits

import Grades.Examples.System.Counts.Timed.RightSided

-- no count grade projects onto time, and a cost model preserves all
-- but the join when time is paired with the counts

import Grades.Examples.System.Counts.Time

------------------------------------------------------------------------
-- Indexed, semidirect and matrix grades
--
-- Grades over maps from names (`Grades.Indexed`), semidirect
-- products (`Grades.SemiDirect`) and mode matrices
-- (`Grades.Matrix`).

-- upper bounds on counts by name, an indexed grade; flow-sensitive
-- levels and windowed schedules, semidirect products

import Grades.Examples.Counts.UpperBound
import Grades.Examples.SemiDirect.FlowLevels
import Grades.Examples.SemiDirect.WindowedSchedules

-- the levels each resource reaches: a trough, a range of net changes
-- and a peak, over the integers with infinities

import Grades.Examples.SemiDirect.ExtendedInteger
import Grades.Examples.SemiDirect.ResourceLevels

-- the costs of switching between the modes of a device, as max-plus
-- mode matrices

import Grades.Examples.SemiDirect.ModeSwitchCosts

-- the time spent in each mode of a device, as mode matrices of
-- realisable boxes of intervals

import Grades.Examples.SemiDirect.ModeTimes.Boxes
import Grades.Examples.SemiDirect.ModeTimes

------------------------------------------------------------------------
-- Worked instances
--
-- All of the above at one alphabet: the orderings between concrete
-- grades and the action of each morphism on them, as checked terms, and
-- example computations typed at the grades.

import Grades.Examples.Worked
