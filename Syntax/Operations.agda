------------------------------------------------------
-- Signature of operation symbols over ground types --
------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.BaseTypes

module Syntax.Operations (Grades : GradeSystem) (BTs : BaseTypes) where

open import Syntax.GroundTypes (Grades) (BTs)

open import Util.Equality

open GradeSystemInterface Grades

-- Bundle of the data describing an operation signature:
-- the set of operation symbols `Op`, their parameter and
-- arity ground types, and the effect grade of performing each.

record Operations : Set₁ where
  field
    Op       : Set                       -- set of operation names
    _≟ₒ_     : DecidableEquality Op      -- operation names have decidable equality
    param    : Op → GType                -- parameter type of each operation
    arity    : Op → GType                -- arity type of each operation
    op-grade : Op → E                    -- effect grade of performing each operation
