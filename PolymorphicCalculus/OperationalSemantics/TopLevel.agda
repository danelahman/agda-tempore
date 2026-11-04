------------------------------------------------------------------
-- Top-level pure semantics of algebraic operations             --
--                                                              --
-- `op-sem op 𝕊 V` is the value an implementation of `op`       --
-- returns for the parameter `V` in the state `𝕊`. A parameter  --
-- typed over a typed state gives a result of the arity type    --
-- after a passage of the operation's grade (`op-sem-typed`).   --
------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.TopLevel (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades              S
open import PolymorphicCalculus.Syntax.Types               S
open import PolymorphicCalculus.Syntax.Contexts            S
open import PolymorphicCalculus.Typing.ScopeClosed         S
open import PolymorphicCalculus.Syntax.Run                 S
open import PolymorphicCalculus.OperationalSemantics.State S

-- Top-level pure semantics of algebraic operations

record TopLevelOpSemantics : Set where
  field
    op-sem       : (op : Op) → ∀ {n} → State n → RunV n → RunV n
    op-sem-typed : (op : Op) → ∀ {n} {𝕊 : State n} {Ψ : StateTyping 𝕊} {V}
                 → Types Ψ
                 → toCtx Ψ ⊢ᵛ V ⦂ ⌜ param op ⌝ᵍ
                 → toCtx Ψ ⟨ rconst ∣ op-grade op ∣ᵉ ⟩ ⊢ᵛ op-sem op 𝕊 V ⦂ ⌜ arity op ⌝ᵍ
