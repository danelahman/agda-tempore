-----------------------------------------------------------------
-- Bundled specification of a concrete instance of the language --
--                                                              --
-- A `LanguageSpec` packages the three pieces of data that the  --
-- syntax and semantics of the language are parameterised over: --
--                                                              --
--   - a grade system for effects and resources,                --
--   - a signature of base types,                               --
--   - an operation signature.                                  --
--                                                              --
-- Downstream syntax and semantics modules take a single        --
-- `LanguageSpec` parameter and open it locally.                --
-----------------------------------------------------------------

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
