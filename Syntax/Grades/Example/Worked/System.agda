------------------------------------------------------------------------
-- Worked instances of the grade systems.                             --
--                                                                    --
-- A grade system pairs effect grades (what a computation may do)     --
-- with resource grades (what is thereby guaranteed about time), with --
-- a monoid morphism `∣_∣ᵉ` from the first to the second; the         --
-- projection determines what the resource grade forgets.             --
--                                                                    --
-- Each module computes the projection on the grades of the sensor    --
-- node and exercises its monotonicity: an ordering between two       --
-- effect grades holds between their images.                          --
--                                                                    --
-- There is one system between time intervals, one for each of the    --
-- four trace grades, one over left-sided time paired with a security --
-- level, and those of the counts. Every trace projection measures a  --
-- set of traces by a duration; the sets are read disjunctively, so a --
-- cap measures its slowest member and a floor its fastest.           --
--                                                                    --
-- An index: one module per system.                                   --
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

-- the rigid finite-expression grades, measured by their duration hull

import Syntax.Grades.Example.Worked.System.Traces.Rigid.Finite.RightSided
import Syntax.Grades.Example.Worked.System.Traces.Rigid.Finite.LeftSided
import Syntax.Grades.Example.Worked.System.Traces.Rigid.Finite.TwoSided

-- the rigid regular-expression grades, measured by their duration hull

import Syntax.Grades.Example.Worked.System.Traces.Rigid.Rational.RightSided
import Syntax.Grades.Example.Worked.System.Traces.Rigid.Rational.LeftSided
import Syntax.Grades.Example.Worked.System.Traces.Rigid.Rational.TwoSided

-- left-sided time and a security level: timed declassification, an
-- embargo alone, and a taint check alone

import Syntax.Grades.Example.Worked.System.Product.LeftSidedTimeLevel

-- the trace and interval grades, projected onto counts

import Syntax.Grades.Example.Worked.System.Counts
