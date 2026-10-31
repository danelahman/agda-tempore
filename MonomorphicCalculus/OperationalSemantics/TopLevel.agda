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
           → {𝕊 : State []} -- uniform in 𝕊 only under `OpSemCoherent`
           → toCtx 𝕊 ⊢V⦂ ⌜ param op ⌝ᵍ
           → toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ⊢V⦂ ⌜ arity op ⌝ᵍ
