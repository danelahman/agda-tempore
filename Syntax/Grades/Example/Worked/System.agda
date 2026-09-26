------------------------------------------------------------------------
-- Worked instances of the grade systems.                              --
--                                                                     --
-- A grade system pairs effect grades (what a computation may do) with --
-- resource grades (what is thereby guaranteed about time) and a       --
-- monoid map `∣_∣ᵉ` projecting the first onto the second. Reading the --
-- projection tells you what the resource grade may forget.            --
--                                                                     --
-- Each module computes the projection on the sensor node's own       --
-- grades and then exercises its monotonicity: an ordering between two --
-- effect grades must still hold between their images.                 --
--                                                                     --
-- There is one between time intervals, one for each of the four trace --
-- grades, and one over left-sided time paired with a security level.  --
-- Every trace projection measures a set of traces by a duration: the  --
-- sets are read disjunctively -- which listed trace was taken is not  --
-- known -- so a cap has to cover the slowest member and a floor may    --
-- promise only the fastest.                                            --
--                                                                     --
-- An index only: one module per system.                                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.System where

-- forgetting the upper bound of a two-sided interval

import Syntax.Grades.Example.Worked.System.IntervalsToLeftSidedIntervals

-- the timed trace grades, measured against time intervals

import Syntax.Grades.Example.Worked.System.Traces.Timed.RightSided
import Syntax.Grades.Example.Worked.System.Traces.Timed.LeftSided
import Syntax.Grades.Example.Worked.System.Traces.Timed.TwoSided

-- the subset cap, beside the timed floor on the same runs

import Syntax.Grades.Example.Worked.System.Traces.Subsets.RightSided

-- left-sided time and a security level: timed declassification, an
-- embargo alone, and a taint check alone

import Syntax.Grades.Example.Worked.System.Product.LeftSidedTimeLevel

-- the trace and interval grades, projected onto counts

import Syntax.Grades.Example.Worked.System.Counts
