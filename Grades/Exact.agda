------------------------------------------------------------------------
-- Exact timed words: runs with exact running times and stretches     --
-- that admit sets of operations. A stretch is a piece of an exact    --
-- word of one length; a time span `e & S` is a letter of an          --
-- expression, whose length lies within an interval and which denotes --
-- the stretches of those lengths admitting the operations of `S`.    --
-- This module is only an index.                                      --
------------------------------------------------------------------------

module Grades.Exact where

-- words, merging of stretches with one set, the monoid, idle waits

import Grades.Exact.Base

-- the order: pointwise comparison of labellings; a preorder that
-- sequencing preserves, antisymmetric on normal words

import Grades.Exact.Order

-- sets of words under the ∀∃ lift: a preorder, a monotone product
-- distributing over joins, greatest elements, the zero-product property

import Grades.Exact.Lift

-- one-sided expressions over interval letters and the sets they denote

import Grades.Exact.Expression

-- shortening and lengthening stretches; upper expressions are closed
-- under the first, lower ones under the second

import Grades.Exact.Resize

-- removing and inserting time, and fitting after resizing

import Grades.Exact.Splice

-- the hull of a run on either side is invisible against bounds of
-- that side

import Grades.Exact.Hull

-- moving within an operation of a word

import Grades.Exact.Offsets

-- in whole steps: words of slots, and the order as slot-by-slot
-- comparison; slots coded as letters

import Grades.Exact.Slots

-- walking two words in step: pouring a word into another is fitting it

import Grades.Exact.Pour

-- words of one-sided letters, their instances as pieces, and where the
-- pieces of a fit lie in time

import Grades.Exact.Letters
import Grades.Exact.Positions

-- the pouring reader, in both instances, and moving its runs between
-- readings of the same words

import Grades.Exact.Reader
import Grades.Exact.Reader.Transfer

-- the upper reader: building a word of the bound from a run, reading a
-- fit as a run, closing the bounds, runs near the upper ends, smaller
-- weights; sound and complete, against several bounds at once

import Grades.Exact.Reader.Upper
import Grades.Exact.Reader.Upper.Build
import Grades.Exact.Reader.Upper.Read
import Grades.Exact.Reader.Upper.Close
import Grades.Exact.Reader.Upper.Zone
import Grades.Exact.Reader.Upper.Mimic
import Grades.Exact.Reader.Upper.Correct

-- the lower reader, likewise

import Grades.Exact.Reader.Lower
import Grades.Exact.Reader.Lower.Build
import Grades.Exact.Reader.Lower.Read
import Grades.Exact.Reader.Lower.Close
import Grades.Exact.Reader.Lower.Zone
import Grades.Exact.Reader.Lower.Mimic
import Grades.Exact.Reader.Lower.Correct

-- finite expressions: their words, the decision of their order, and
-- the grades they form in each instance

import Grades.Exact.Finite
import Grades.Exact.Finite.Grades

-- the trace grades with banked delays as instances: allowances as upper
-- expressions, guarantees as lower ones (the maps of grades are
-- `Grades.Examples.Traces.Banked.ExactGrades`)

import Grades.Exact.Banked.Base
import Grades.Exact.Banked.Upper
import Grades.Exact.Banked.Lower

-- regular expressions over a common time unit: units and scaling,
-- unbounded stretches unrolled, the words of an expression with star,
-- and both readers complete against a family of grid words

import Grades.Exact.Grid
import Grades.Exact.Grid.NonNegativeRational
import Grades.Exact.Regular.Unroll
import Grades.Exact.Regular.Words
import Grades.Exact.Reader.Upper.Family
import Grades.Exact.Reader.Lower.Family

-- the readers moved along maps of pieces and bounds; the gap of a
-- chain in whole steps; the readers against a regular set of bounds as
-- determinised automata of configurations; and the order on
-- expressions with iteration, decided

import Grades.Exact.Reader.Rename
import Grades.Exact.Regular.Gap
import Grades.Exact.Regular.Upper
import Grades.Exact.Regular.Lower
import Grades.Exact.Regular.Decide

-- expressions with iteration as grades in each instance, with the
-- Kleene plus `e · e*`

import Grades.Exact.Regular.Grades

-- the duration hull of an expression, and the intervals whose ends some
-- run fits

import Grades.Exact.Durations
import Grades.Exact.Finite.Durations
import Grades.Exact.Finite.Interval

-- interval grades of consistent pairs, for any lower and upper grades
-- of sets of runs; those of expressions with iteration

import Grades.Exact.Interval
import Grades.Exact.Regular.Interval

-- the duration hull of the timed regex grades

import Grades.Exact.Regular.Durations

-- a lower and an upper end walked together: the walk, its zones, and
-- the decision of whether they have a common run

import Grades.Exact.Joint
import Grades.Exact.Joint.Complete
import Grades.Exact.Joint.Zone
import Grades.Exact.Joint.Zoned
import Grades.Exact.Joint.Scale
import Grades.Exact.Joint.Decide
