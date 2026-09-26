------------------------------------------------------------------------
-- Example grades, and example grade systems built from them.          --
--                                                                     --
-- A `Grade` (see `Syntax.Grades`) is an ordered monoid with an        --
-- inclusion of ℕ as "so many time steps". A `GradeSystem` is a pair   --
-- of them (effect grades, recording what a computation may do, and    --
-- resource grades, recording what is thereby guaranteed about time)   --
-- together with a monoid map projecting the first onto the second.    --
--                                                                     --
-- The examples come in four families:                                 --
--                                                                     --
--   * `Time.*` -- grades that measure only elapsed time, as a bound   --
--     or a window of time steps, over ℕ or, in `Time.Dense.*`, over   --
--     the non-negative rationals ℚ≥0; morphisms embed the discrete    --
--     grades in the dense ones. Small and self-contained.             --
--                                                                     --
--   * `Traces.*` -- grades that record *which runs* a computation     --
--     may have had, as a set of timed traces, sharing their carrier   --
--     and monoid (from `Grades.Traces.Sets`) and differing in the     --
--     order they put on it.                                           --
--                                                                     --
--   * `Counts.*` -- grades that count, per operation (or per class    --
--     under a coarser index into `Fin n`), how often a computation    --
--     draws on each; `AtMost`/`AtLeast` are quotas and guarantees,    --
--     `Power` the generic `n`-counter product.                        --
--                                                                     --
--   * `SecurityLevel` -- a decidable join-semilattice of levels,      --
--     floating upward as data is touched; the two-point `Low < High`  --
--     and taint sets over `Fin n`.                                    --
--                                                                     --
-- `Product.*` pairs members of these families, using the generic      --
-- product of grades in `Syntax.Grades.Product`: left- and right-sided --
-- time with a security level, and right-sided time with an energy     --
-- budget (right-sided time again, read as spend rather than elapsed   --
-- time).                                                              --
--                                                                     --
-- The trace family splits in two: `Timed.*` over the cost-sensitive   --
-- orders on traces, with a floor, a cap and their pairing, and        --
-- `Subsets.*` over equality, with a cap.                              --
--                                                                     --
-- Every grade carries its greatest element in its own carrier: the    --
-- unit for the left-sided intervals and the coverage floor,           --
-- `[ 0 , ∞ ]` for the two-sided intervals, and a point of its own,    --
-- then absorbing, for the allowance cap and the subset cap.           --
--                                                                     --
-- `System.*` pairs them up: each projection says what a resource      --
-- grade may forget about the effect grade it comes from, and an       --
-- absorbing top has to land on an absorbing top.                      --
--                                                                     --
-- An index only: the trace-based examples are parameterised by the    --
-- alphabet `Op`, so it lists the pieces rather than re-exporting      --
-- them.                                                               --
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

-- the same three shapes over the non-negative rationals ℚ≥0, with
-- morphisms embedding the discrete grades above

import Syntax.Grades.Example.Time.Dense.NonNegativeRational
import Syntax.Grades.Example.Time.Dense.ExtendedRational
import Syntax.Grades.Example.Time.Dense.LeftSided
import Syntax.Grades.Example.Time.Dense.RightSided
import Syntax.Grades.Example.Time.Dense.TwoSided
import Syntax.Grades.Example.Time.Dense.Examples

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
-- says what weakening one is allowed to ask for instead. `Traces` is
-- the index.

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

-- worked instances at the sensor node

import Syntax.Grades.Example.Counts.Worked

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

-- the allowance cap does not project onto quotas: a bound's delays pay
-- for its operations, so no morphism into at-most counts can count
-- what the bound permits

import Syntax.Grades.Example.System.Counts.Timed.RightSided

-- why no count grade projects onto time, and what a cost model
-- preserves when time is paired with the counts

import Syntax.Grades.Example.System.Counts.Time

------------------------------------------------------------------------
-- Worked instances
--
-- All of the above at one fixed alphabet, with the orderings that hold
-- between concrete grades and the effect of each morphism on them
-- exhibited as checked terms, and example computations typed against
-- the grades. A reader's tour of this whole subtree.

import Syntax.Grades.Example.Worked
