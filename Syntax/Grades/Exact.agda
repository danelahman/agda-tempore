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
