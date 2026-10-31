open import Grades.Base
open import Language.Spec
open import Language.Operations

module MonomorphicCalculus.OperationalSemantics.TopLevel (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           S
open import MonomorphicCalculus.OperationalSemantics.State                S

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Terms    S
open import MonomorphicCalculus.Syntax.Types    S

-- TopLevel pure semantics of algebraic operations

record TopLevelOpSemantics : Set where
  field 
    op-sem : (op : Op)
           → {S : 𝕊 []} -- uniform in S only under `OpSemCoherent`
           → toCtx S ⊢V⦂ type-of-gtype (param op)
           → toCtx S ⟨ ∣ op-grade op ∣ᵉ ⟩ ⊢V⦂ type-of-gtype (arity op)
