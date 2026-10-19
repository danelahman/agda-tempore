open import Data.Product

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.TopLevelPreservationTheorem (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem  S
open import OperationalSemantics.State                S
open import OperationalSemantics.TopLevelOpSemantics  S

open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.RenActions    S
open import Syntax.Renamings     S
open import Syntax.Substitutions S
open import Syntax.Types         S


-- Top-level small-step operational semantics aka Preservation theorem,
-- using the pure semantics of algebraic operations.

module PureTopLevelPreservationTheorem (OpSemantics : TopLevelOpSemantics) where

  open TopLevelOpSemantics OpSemantics

  data _⟿_ :  {C D : CType} → Config C → Config D → Set where

    -- Step according to the ordinary small-step semantics
    ↝-STEP : ∀ {A B ε ε'}
           → {S S' : 𝕊 []}
           → {M : (toCtx S ⊢C⦂ A ‼ ε)}
           → {N : (toCtx S' ⊢C⦂ B ‼ ε')}
           → ⟨ S , M ⟩ ↝ ⟨ S' , N ⟩
           → ⟨ S , M ⟩ ⟿ ⟨ S' , N ⟩

    -- Run a top-level implementation of an algebraic operation
    OP-STEP : ∀ {A ε op}
            → {S : 𝕊 []} 
            → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
            → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε} 
            → ⟨ S , perform op V M ⟩ ⟿
              ⟨ grade-pass S (mapᵉ (op-grade op)) , M [ split-[] ↦ op-sem op V ]c ⟩

  -- Reflexive-transitive closure: a run of the top-level machine.

  infixr 5 _◅ᵗ_

  data _⟿*_ : ∀ {A B ε ε'} → Config (A ‼ ε) → Config (B ‼ ε') → Set where
    ε*ᵗ  : ∀ {A ε} {cf : Config (A ‼ ε)}
         → cf ⟿* cf
    _◅ᵗ_ : ∀ {A B C ε₁ ε₂ ε₃}
         → {cf₁ : Config (A ‼ ε₁)} → {cf₂ : Config (B ‼ ε₂)} → {cf₃ : Config (C ‼ ε₃)}
         → cf₁ ⟿ cf₂ → cf₂ ⟿* cf₃ → cf₁ ⟿* cf₃

  -- invariants preserved by the top-level small-step operational semantics
  -- in particular, running a top-level implementation of an algebraic operation
  -- results in an equality S' · ε' ≡ S · ε
  
  top-level-step-invariants : ∀ {A B ε ε'}
                            → {S S' : 𝕊 []}
                            → {M : toCtx S ⊢C⦂ A ‼ ε}
                            → {M' : toCtx S' ⊢C⦂ B ‼ ε'}
                            → ⟨ S , M ⟩ ⟿ ⟨ S' , M' ⟩
                            → B <:ᵛ A
                            × state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε

  top-level-step-invariants (↝-STEP step) =
    step-invariants step
  top-level-step-invariants {A = A} {S = S} OP-STEP =
    <:ᵛ-refl A ,
    ≃ᵣ⇒≾ᵣ
      (≃ᵣ-trans (·ᵣ-assoc _ _ _) (·ᵣ-cong ≃ᵣ-refl (≃ᵣ-sym map-·ᵉ)))
