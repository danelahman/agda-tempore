open import Data.Empty

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.TopLevelProgressTheorem (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem         S
open import OperationalSemantics.ProgressTheorem             S
open import OperationalSemantics.State                       S
open import OperationalSemantics.TopLevelOpSemantics         S
open import OperationalSemantics.TopLevelPreservationTheorem S

open import Syntax.Contexts S
open import Syntax.Language S
open import Syntax.Types    S

-- Progress theorem at the top-level: a term is just a returned value or makes a reduction step,
-- using the pure semantics of algebraic operations.

module PureTopLevelProgressTheorem (OpSemantics : TopLevelOpSemantics) where
  open PureTopLevelPreservationTheorem (OpSemantics)

  data TopLevelProgresses : {ε : E}
                          → {S : 𝕊 []}
                          → {A : VType}
                          → (M : toCtx S ⊢C⦂ A ‼ ε)
                          → Set where

       is-top-level-value : {S : 𝕊 []}
                          → {A : VType}
                          → {V : toCtx S ⊢V⦂ A}
                          -----------------------------
                          → TopLevelProgresses (return V)

       top-level-steps    : ∀ {ε ε'}
                          → {A B : VType}
                          → {S S' : 𝕊 []}
                          → {M : toCtx S ⊢C⦂ A ‼ ε}
                          → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                          → (prf : state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε)
                          → (t : B <:ᵛ A)
                          → ⟨ S , M ⟩ ⟿ ⟨ S' , M' ⟩
                          ------------------------------------------------------------
                          → TopLevelProgresses M

  -- Top-level progress theorem statement
  
  top-level-progress : ∀ {A ε} → {S : 𝕊 []} → (M : toCtx S ⊢C⦂ A ‼ ε) → TopLevelProgresses M
  top-level-progress {S = S} M with progress M
  ... | is-value =
    is-top-level-value
  ... | is-op =
    top-level-steps
      (≃ᵣ⇒≾ᵣ (≃ᵣ-trans (·ᵣ-assoc _ _ _) (·ᵣ-cong ≃ᵣ-refl (≃ᵣ-sym map-·ᵉ))))
      (<:ᵛ-refl _)
      OP-STEP
  ... | steps M↝M' p t =
    top-level-steps (cancelled⇒total (step-extends-state M↝M') p) t (↝-STEP M↝M')
