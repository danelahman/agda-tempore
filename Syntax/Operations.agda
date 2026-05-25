------------------------------------------------------
-- Signature of operation symbols over ground types --
------------------------------------------------------

open import Syntax.Grades
open import Syntax.BaseTypes

module Syntax.Operations (Grades : GradeSystem) (BTs : BaseTypes) where

open import Util.Equality
open import Syntax.GroundTypes (Grades) (BTs)

open GradeSystemInterface Grades

-- Bundle of the data describing an operation signature:
-- the set of operation symbols `Op`, their parameter and
-- arity ground types, and their (maximal) execution durations.

record Operations : Set₁ where
  field
    Op        : Set                       -- set of operation symbols
    param     : Op → GType                -- parameter type of each operation
    arity     : Op → GType                -- arity type of each operation
    op-grade  : Op → E                    -- each operation's (maximal) duration
