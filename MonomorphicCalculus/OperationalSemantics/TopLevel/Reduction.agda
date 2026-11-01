open import Data.Product

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.TopLevel.Reduction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           S
open import MonomorphicCalculus.OperationalSemantics.State               S
open import MonomorphicCalculus.OperationalSemantics.TopLevel            S
open import MonomorphicCalculus.OperationalSemantics.TypeSafety          S

open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming.Action S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Substitution    S
open import MonomorphicCalculus.Syntax.Types           S


-- Top-level small-step operational semantics, using the pure semantics
-- of algebraic operations; being typed, it is also preservation.

module PureTopLevelPreservationTheorem (OpSemantics : TopLevelOpSemantics) where

  open TopLevelOpSemantics OpSemantics

  data _⟶ᵗ_ : {C D : CType} → Config C → Config D → Set where

    -- Step according to the ordinary small-step semantics
    STEP : ∀ {A B ε ε'}
         → {𝕊 𝕊' : State []}
         → {M : (toCtx 𝕊 ⊢ᶜ⦂ A ! ε)}
         → {N : (toCtx 𝕊' ⊢ᶜ⦂ B ! ε')}
         → ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ N ⟩
         → ⟨ 𝕊 ∣ M ⟩ ⟶ᵗ ⟨ 𝕊' ∣ N ⟩

    -- Run a top-level implementation of an algebraic operation
    OP-STEP : ∀ {A ε op}
            → {𝕊 : State []} 
            → {V : (toCtx 𝕊) ⊢ᵛ⦂ ⌜ param op ⌝ᵍ} 
            → {M : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢ᶜ⦂ A ! ε} 
            → ⟨ 𝕊 ∣ perform op V M ⟩ ⟶ᵗ
              ⟨ grade-pass 𝕊 (∣ op-grade op ∣ᵉ) ∣ M [ op-sem op V ]₀ ⟩

  -- Reflexive-transitive closure: a run of the top-level machine.

  infixr 5 _▸_

  data _⟶*ᵗ_ : ∀ {A B ε ε'} → Config (A ! ε) → Config (B ! ε') → Set where
    done : ∀ {A ε} {cf : Config (A ! ε)}
         → cf ⟶*ᵗ cf
    _▸_  : ∀ {A B C ε₁ ε₂ ε₃}
         → {cf₁ : Config (A ! ε₁)} → {cf₂ : Config (B ! ε₂)} → {cf₃ : Config (C ! ε₃)}
         → cf₁ ⟶ᵗ cf₂ → cf₂ ⟶*ᵗ cf₃ → cf₁ ⟶*ᵗ cf₃

  -- invariants preserved by the top-level small-step operational semantics;
  -- running a top-level implementation of an algebraic operation gives an
  -- equality 𝕊' · ε' ≡ 𝕊 · ε
  
  top-level-step-invariants : ∀ {A B ε ε'}
                            → {𝕊 𝕊' : State []}
                            → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
                            → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
                            → ⟨ 𝕊 ∣ M ⟩ ⟶ᵗ ⟨ 𝕊' ∣ M' ⟩
                            → B <:ᵛ A
                            × state-grade 𝕊' ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ state-grade 𝕊 ·ᵣ ∣ ε ∣ᵉ

  top-level-step-invariants (STEP step) =
    Preserved.subtype (preservation step) ,
    cancelled⇒total (step-extends-state step) (Preserved.grade (preservation step))
  top-level-step-invariants {A = A} {𝕊 = 𝕊} OP-STEP =
    <:ᵛ-refl A ,
    ≃ᵣ⇒≾ᵣ
      (≃ᵣ-trans (·ᵣ-assoc _ _ _) (·ᵣ-cong ≃ᵣ-refl (≃ᵣ-sym map-·ᵉ)))
