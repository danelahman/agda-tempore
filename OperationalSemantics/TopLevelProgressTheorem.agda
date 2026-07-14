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

-- Progress theorem at the top-level: a term is just a returned value or makes a reduction step.

-- Note: These first results work with the pure semantics of algebraic operations

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
                          → {A : VType}
                          → {S S' : 𝕊 []}
                          → {M : toCtx S ⊢C⦂ A ‼ ε}
                          → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
                          → (prf : state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε)
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
      (≾ᵣ-reflexive (trans (·ᵣ-assoc _ _ _) (cong (state-grade S ·ᵣ_) (sym map-·ᵉ))))
      OP-STEP
  ... | steps M↝M' p =
    top-level-steps (cancelled⇒total (step-extends-state M↝M') p) (↝-STEP M↝M')


-- Note: These results work with the monadic semantics of algebraic operations

open import Util.Monad

module MonadicTopLevelProgressTheorem
         {monad : GradedMonad EGrade}
         (MonadicOpSemantics : TopLevelMonadicOpSemantics monad) where

  open TopLevelMonadicOpSemantics MonadicOpSemantics
  open MonadicTopLevelPreservationTheorem {monad} (MonadicOpSemantics)

  open GradedMonad monad

  data TopLevelMonadicProgresses : {ε : E}
                                 → {S : 𝕊 []}
                                 → {A : VType}
                                 → (M : toCtx S ⊢C⦂ A ‼ ε)
                                 → Set where

       is-top-level-valueₘ : {S : 𝕊 []}
                           → {A : VType}
                           → {V : toCtx S ⊢V⦂ A}
                           ------------------------------------
                           → TopLevelMonadicProgresses (return V)

       top-level-stepsₘ : ∀ {ε ε'}
                        → {A : VType}
                        → {S S' : 𝕊 []}
                        → {M  : toCtx S  ⊢C⦂ A ‼ ε}
                        → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
                        → (prf : state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε)
                        → ⟨ S , M ⟩ ⟿ₘ returnM (⟨ S' , M' ⟩)
                        ------------------------------------------------------------
                        → TopLevelMonadicProgresses M

       top-level-steps-opₘ : ∀ {ε op}
                           → {A : VType}
                           → {S : 𝕊 []}
                           → {V : toCtx S ⊢V⦂ type-of-gtype (param op)}
                           → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε}
                           -------------------------------------------------------------------------
                           → TopLevelMonadicProgresses (perform op V M)


  top-level-progressₘ : ∀ {A ε} → {S : 𝕊 []} → (M : toCtx S ⊢C⦂ A ‼ ε) → TopLevelMonadicProgresses M
  top-level-progressₘ {S = S} M with progress M
  ... | is-value     = is-top-level-valueₘ
  ... | is-op        = top-level-steps-opₘ
  ... | steps M↝M' p = top-level-stepsₘ (cancelled⇒total (step-extends-state M↝M') p) (↝-STEPₘ M↝M')
