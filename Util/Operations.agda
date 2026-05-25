------------------------------------------------------
-- Signature of operation symbols over ground types --
------------------------------------------------------

open import Syntax.Grades
open import Util.BaseTypes

module Util.Operations (Grades : GradeSystem) (BTs : BaseTypes) where

open import Util.Equality
open import Util.GroundTypes (Grades) (BTs)

open GradeSystemInterface Grades

-- Signature of (ground-typed) operation symbols

postulate
  Op        : Set                          -- set of operation symbols
  param     : Op → GType                   -- parameter type of each operation
  arity     : Op → GType                   -- arity type of each operation
  op-grade  : Op → E                       -- each operation's (maximal) duration
