open import Grades.Base
open import Language.Spec
open import Language.Operations

module ClosedCalculus.OperationalSemantics.TopLevelOpSemantics (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.OperationalSemantics.PreservationTheorem S
open import ClosedCalculus.OperationalSemantics.State                S

open import ClosedCalculus.Syntax.Contexts S
open import ClosedCalculus.Syntax.Terms    S
open import Language.Types                 S

-- TopLevel pure semantics of algebraic operations

record TopLevelOpSemantics : Set where
  field 
    op-sem : (op : Op)
           → {S : 𝕊 []} -- TODO: formally requires a naturality condition; needs to be parametric in S
           → toCtx S ⊢V⦂ type-of-gtype (param op)
           → toCtx S ⟨ mapᵉ (op-grade op) ⟩ ⊢V⦂ type-of-gtype (arity op)
