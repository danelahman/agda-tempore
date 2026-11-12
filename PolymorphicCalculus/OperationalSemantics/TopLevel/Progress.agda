------------------------------------------------------------------
-- Progress of the top-level reduction                          --
--                                                              --
-- A configuration typed at `X ! ε` over a typed state is a     --
-- returned value or makes a top-level step, a step of the      --
-- reduction or an operation call run by its top-level          --
-- implementation, that preserves its typing                    --
-- (`top-level-progress`).                                      --
------------------------------------------------------------------

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.OperationalSemantics.TopLevel.Progress (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades                            S
open import PolymorphicCalculus.Syntax.Types                             S
open import PolymorphicCalculus.Typing.ScopeClosed                       S
open import PolymorphicCalculus.Syntax.Run                               S
open import PolymorphicCalculus.OperationalSemantics.State               S
open import PolymorphicCalculus.OperationalSemantics.Reduction           S
open import PolymorphicCalculus.OperationalSemantics.TopLevel            S
open import PolymorphicCalculus.OperationalSemantics.TopLevel.Reduction  S
open import PolymorphicCalculus.OperationalSemantics.TypeSafety          S

-- Progress at the top level: a term is a returned value or makes a reduction
-- step, using the pure semantics of algebraic operations.

module PureTopLevelProgressTheorem (OpSemantics : TopLevelOpSemantics) where
  open PureTopLevelPreservationTheorem (OpSemantics)

  data TopLevelProgresses {n} {𝕊 : State n} (Ψ : StateTyping 𝕊) (X : OVType ∅ˢ) (ε : EExp ∅ˢ)
                          : RunC n → Set where

       is-top-level-value : ∀ {V}
                          -----------------------------------
                          → TopLevelProgresses Ψ X ε (return V)

       top-level-steps    : ∀ {m} {𝕊' : State m} {e : 𝕊 ≤ₛ 𝕊'} {M M'}
                          → Preserved e Ψ M' X ε
                          → ⟨ 𝕊 ∣ M ⟩⟶ᵗ[ e ]⟨ 𝕊' ∣ M' ⟩
                          ---------------------------------
                          → TopLevelProgresses Ψ X ε M

  -- Top-level progress theorem statement

  top-level-progress : ∀ {n} {𝕊 : State n} {Ψ : StateTyping 𝕊} {M X ε}
                     → Types Ψ → (D : toCtx Ψ ⊢ᶜ M ⦂ X ! ε) → TopLevelProgresses Ψ X ε M
  top-level-progress T D with progress D
  ... | inj₁ (is-return V) =
    is-top-level-value
  ... | inj₁ (is-perform op V M') =
    top-level-steps (top-level-preservation T D OP-STEP) OP-STEP
  ... | inj₂ (_ , _ , _ , _ , s) =
    top-level-steps (preservation T D s) (STEP s)
