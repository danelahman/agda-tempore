------------------------------------------------------------------------
-- Exact timed words: runs with exact running times and stretches    --
-- that admit sets of operations. This module is only an index.      --
------------------------------------------------------------------------

module Syntax.Grades.Exact where

-- words, merging of stretches with one set, the monoid, strict waits

import Syntax.Grades.Exact.Base

-- the order: pointwise comparison of labellings; a preorder that
-- sequencing preserves, antisymmetric on normal words

import Syntax.Grades.Exact.Order

-- sets of words under the ∀∃ lift: a preorder, a monotone product
-- distributing over joins, greatest elements, the zero-product property

import Syntax.Grades.Exact.Lift

-- one-sided expressions over interval letters and the sets they denote

import Syntax.Grades.Exact.Expression

-- shortening and lengthening stretches; upper expressions are closed
-- under the first, lower ones under the second

import Syntax.Grades.Exact.Resize

-- removing and inserting time, and fitting after resizing

import Syntax.Grades.Exact.Splice

-- the hull of a run on either side is invisible against bounds of
-- that side

import Syntax.Grades.Exact.Hull

-- moving within an operation of a word

import Syntax.Grades.Exact.Offsets

-- in whole steps: words of slots, and the order as slot-by-slot
-- comparison; slots coded as letters

import Syntax.Grades.Exact.Slots

-- walking two words in step: pouring a word into another is fitting it

import Syntax.Grades.Exact.Pour

-- words of one-sided letters, their instances as pieces, and where the
-- pieces of a fit lie in time

import Syntax.Grades.Exact.Letters
import Syntax.Grades.Exact.Positions

-- the pouring reader, in both instances, and moving its runs between
-- readings of the same words

import Syntax.Grades.Exact.Reader
import Syntax.Grades.Exact.Reader.Transfer

-- the upper reader: building a word of the bound from a run, reading a
-- fit as a run, closing the bounds, runs near the upper ends, smaller
-- weights; sound and complete, against several bounds at once

import Syntax.Grades.Exact.Reader.Upper
import Syntax.Grades.Exact.Reader.Upper.Build
import Syntax.Grades.Exact.Reader.Upper.Read
import Syntax.Grades.Exact.Reader.Upper.Close
import Syntax.Grades.Exact.Reader.Upper.Zone
import Syntax.Grades.Exact.Reader.Upper.Mimic
import Syntax.Grades.Exact.Reader.Upper.Correct

-- the lower reader, likewise

import Syntax.Grades.Exact.Reader.Lower
import Syntax.Grades.Exact.Reader.Lower.Build
import Syntax.Grades.Exact.Reader.Lower.Read
import Syntax.Grades.Exact.Reader.Lower.Close
import Syntax.Grades.Exact.Reader.Lower.Zone
import Syntax.Grades.Exact.Reader.Lower.Mimic
import Syntax.Grades.Exact.Reader.Lower.Correct

-- finite expressions: their words, the decision of their order, and
-- the preordered grades they form in each instance

import Syntax.Grades.Exact.Finite
import Syntax.Grades.Exact.Finite.Grades
