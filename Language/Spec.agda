------------------------------------------------------------------
-- Bundled specification of a concrete instance of the language --
--                                                              --
-- A `LanguageSpec` packages what the syntax and semantics are  --
-- parameterised over: a grade system for effects and           --
-- resources, a signature of base types, and an operation       --
-- signature. Modules take one `LanguageSpec` parameter and     --
-- open it.                                                     --
------------------------------------------------------------------

open import Grades.Base
open import Language.BaseTypes
open import Language.Operations

module Language.Spec where

record LanguageSpec : Set₂ where
  field
    Grades : GradeSystem
    BTs    : BaseTypes
    Ops    : Operations Grades BTs

-- The language without base types, over a grade system and an operation
-- signature

withoutBaseTypes : (Grades : GradeSystem) → Operations Grades noBaseTypes → LanguageSpec
withoutBaseTypes G O = record { Grades = G ; BTs = noBaseTypes ; Ops = O }
