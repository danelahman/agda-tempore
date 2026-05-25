-------------------------------------------------------------
-- Ground types (used as parameter and arity types of      --
-- algebraic operations)                                   --
-------------------------------------------------------------

open import Syntax.Grades
open import Util.BaseTypes

module Util.GroundTypes (Grades : GradeSystem) (BTs : BaseTypes) where

open GradeSystemInterface Grades
open BaseTypes BTs

data GType : Set where
  Base   : BaseType → GType                -- base types
  Unit   : GType                           -- unit type
  Empty  : GType                           -- empty type
  _|×|ᵍ_ : GType → GType → GType           -- product type
  [_]ᵍ_  : R → GType → GType               -- temporal modality: values of type `[ ρ ] A`
                                           -- become available in at most `r` steps
infix 38 _|×|ᵍ_
infix 37 [_]ᵍ_
