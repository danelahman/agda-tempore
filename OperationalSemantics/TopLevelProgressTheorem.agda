open import Syntax.Grades

module OperationalSemantics.TopLevelProgressTheorem (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import OperationalSemantics.PreservationTheorem (Grades)
open import OperationalSemantics.State (Grades)
open import OperationalSemantics.TopLevelOpSemantics (Grades)
open import OperationalSemantics.TopLevelPreservationTheorem (Grades)
open import OperationalSemantics.ProgressTheorem (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Types (Grades)

open import Data.Empty
open import Util.Equality
open import Util.Operations (Grades)

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
  ... | steps p M↝M' =
    top-level-steps p (↝-STEP M↝M')


-- Note: These results work with the monadic semantics of algebraic operations

open import Util.Monad

module MonadicTopLevelProgressTheorem {monad : Monad} (MonadicOpSemantics : TopLevelMonadicOpSemantics monad) where

  open TopLevelMonadicOpSemantics MonadicOpSemantics
  open MonadicTopLevelPreservationTheorem {monad} (MonadicOpSemantics)

  open Monad monad

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
  ... | steps p M↝M' = top-level-stepsₘ p (↝-STEPₘ M↝M')
