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

  data _⟿_ :  {C D : CType} → Config C → Config D → Set where

    -- Step according to the ordinary small-step semantics
    ⟶-STEP : ∀ {A B ε ε'}
           → {S S' : 𝕊 []}
           → {M : (toCtx S ⊢C⦂ A ! ε)}
           → {N : (toCtx S' ⊢C⦂ B ! ε')}
           → ⟨ S , M ⟩ ⟶ ⟨ S' , N ⟩
           → ⟨ S , M ⟩ ⟿ ⟨ S' , N ⟩

    -- Run a top-level implementation of an algebraic operation
    OP-STEP : ∀ {A ε op}
            → {S : 𝕊 []} 
            → {V : (toCtx S) ⊢V⦂ ⌜ param op ⌝ᵍ} 
            → {M : toCtx S ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A ! ε} 
            → ⟨ S , perform op V M ⟩ ⟿
              ⟨ grade-pass S ∣ op-grade op ∣ᵉ , M [ split-[] ↦ op-sem op V ]c ⟩

  -- Reflexive-transitive closure: a run of the top-level machine.

  infixr 5 _◅ᵗ_

  data _⟿*_ : ∀ {A B ε ε'} → Config (A ! ε) → Config (B ! ε') → Set where
    ε*ᵗ  : ∀ {A ε} {cf : Config (A ! ε)}
         → cf ⟿* cf
    _◅ᵗ_ : ∀ {A B C ε₁ ε₂ ε₃}
         → {cf₁ : Config (A ! ε₁)} → {cf₂ : Config (B ! ε₂)} → {cf₃ : Config (C ! ε₃)}
         → cf₁ ⟿ cf₂ → cf₂ ⟿* cf₃ → cf₁ ⟿* cf₃

  -- invariants preserved by the top-level small-step operational semantics;
  -- running a top-level implementation of an algebraic operation gives an
  -- equality S' · ε' ≡ S · ε
  
  top-level-step-invariants : ∀ {A B ε ε'}
                            → {S S' : 𝕊 []}
                            → {M : toCtx S ⊢C⦂ A ! ε}
                            → {M' : toCtx S' ⊢C⦂ B ! ε'}
                            → ⟨ S , M ⟩ ⟿ ⟨ S' , M' ⟩
                            → B <:ᵛ A
                            × state-grade S' ·ᵣ ∣ ε' ∣ᵉ ≾ᵣ state-grade S ·ᵣ ∣ ε ∣ᵉ

  top-level-step-invariants (⟶-STEP step) =
    step-invariants step
  top-level-step-invariants {A = A} {S = S} OP-STEP =
    <:ᵛ-refl A ,
    ≃ᵣ⇒≾ᵣ
      (≃ᵣ-trans (·ᵣ-assoc _ _ _) (·ᵣ-cong ≃ᵣ-refl (≃ᵣ-sym map-·ᵉ)))
