open import Data.Empty

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.TopLevel.Progress (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction                   S
open import MonomorphicCalculus.OperationalSemantics.Progress                    S
open import MonomorphicCalculus.OperationalSemantics.State                       S
open import MonomorphicCalculus.OperationalSemantics.TopLevel                    S
open import MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction          S

open import MonomorphicCalculus.Syntax.Contexts S
open import MonomorphicCalculus.Syntax.Terms    S
open import MonomorphicCalculus.Syntax.Types    S

-- Progress at the top level: a term is a returned value or makes a reduction
-- step, using the pure semantics of algebraic operations.

module PureTopLevelProgressTheorem (OpSemantics : TopLevelOpSemantics) where
  open PureTopLevelPreservationTheorem (OpSemantics)

  data TopLevelProgresses : {ε : E}
                          → {𝕊 : State []}
                          → {A : VType}
                          → (M : toCtx 𝕊 ⊢C⦂ A ! ε)
                          → Set where

       is-top-level-value : {𝕊 : State []}
                          → {A : VType}
                          → {V : toCtx 𝕊 ⊢V⦂ A}
                          -----------------------------
                          → TopLevelProgresses (return V)

       top-level-steps    : ∀ {ε ε'}
                          → {A B : VType}
                          → {𝕊 𝕊' : State []}
                          → {M : toCtx 𝕊 ⊢C⦂ A ! ε}
                          → {M' : toCtx 𝕊' ⊢C⦂ B ! ε'}
                          → (prf : state-grade 𝕊' ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ state-grade 𝕊 ·ᵣ ∣ ε ∣ᵉ)
                          → (t : B <:ᵛ A)
                          → ⟨ 𝕊 ∣ M ⟩ ⟶ᵗ ⟨ 𝕊' ∣ M' ⟩
                          ------------------------------------------------------------
                          → TopLevelProgresses M

  -- Top-level progress theorem statement
  
  top-level-progress : ∀ {A ε} → {𝕊 : State []} → (M : toCtx 𝕊 ⊢C⦂ A ! ε) → TopLevelProgresses M
  top-level-progress {𝕊 = 𝕊} M with progress M
  ... | is-return =
    is-top-level-value
  ... | is-perform =
    top-level-steps
      (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (·ᵣ-assoc _ _ _) (·ᵣ-cong ≃ᵣ-refl (≃ᵣ-sym map-·ᵉ))))
      (<:ᵛ-refl _)
      OP-STEP
  ... | steps M⟶M' p t =
    top-level-steps (cancelled⇒total (step-extends-state M⟶M') p) t (STEP M⟶M')
