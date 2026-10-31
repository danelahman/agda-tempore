-------------------------------------------------------------
-- Ground types (used as parameter and arity types of      --
-- algebraic operations)                                   --
-------------------------------------------------------------

open import Grades.Base
open import Language.BaseTypes

module Language.GroundTypes (Grades : GradeSystem) (BTs : BaseTypes) where

open GradeSystemInterface Grades
open BaseTypes BTs

data GType : Set where
  Base   : BaseType → GType                -- base types
  unit   : GType                           -- unit type
  bool   : GType                           -- boolean type
  nat    : GType                           -- natural-number type
  empty  : GType                           -- empty type
  _|×|ᵍ_ : GType → GType → GType           -- product type
  _|+|ᵍ_ : GType → GType → GType           -- sum type
  listᵍ  : GType → GType                   -- list type
  [_]ᵍ_  : R → GType → GType               -- box modality: values of type `[ ρ ]ᵍ A`
                                           -- become available in at most `ρ` steps
infix 38 _|×|ᵍ_ _|+|ᵍ_
infix 37 [_]ᵍ_
