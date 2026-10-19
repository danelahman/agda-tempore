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
