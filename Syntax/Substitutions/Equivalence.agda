------------------------------------------------------------------------
-- Substitution against the term equivalence.                         --
--                                                                    --
-- `↝` respects `_≐ᶜ_`, and almost every reduction rule's reduct is a  --
-- substitution, so substitution must be a congruence for it.          --
--                                                                    --
-- The one clause with content is `⟨_,_⟩[_↦_]var`, which crosses a     --
-- lock by weakening along a renaming built from the *grade bound*:    --
-- the two sides carry different bounds, related by `bound-irr`.       --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_; yes; no)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions.Equivalence (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec

-- ETERNAL VALUES

eternal-val-ext-cong : ∀ {Γ A ρ} → (et : Eternal A) → {V V' : Γ ⊢V⦂ A}
                     → V ≐ᵛ V'
                     → eternal-val-ext {ρ = ρ} et V ≐ᵛ eternal-val-ext et V'
eternal-val-ext-cong et = cong (eternal-val-ext et)

eternal-val-restrict-cong : ∀ {Γ A} → (et : Eternal A) → {V V' : Γ ⊢V⦂ A}
                          → V ≐ᵛ V'
                          → eternal-val-restrict et V ≐ᵛ eternal-val-restrict et V'
eternal-val-restrict-cong et = cong (eternal-val-restrict et)

-- SUBSTITUTING INTO A VARIABLE
--
-- The substitution reads the variable's grade bound (at the lock case, to build
-- a `⟨⟩-≤-ren`), so the two bounds must be identified — by `bound-irr`.

sub-var-≐ : ∀ {Γ A B ρ ρ'}
          → (y : B ∈[ ρ' ] Γ) → (f f' : ¬ Eternal B → ρ' ≾ᵣ uᵣ)
          → (x : A ∈[ ρ ] Γ) → {W W' : split-l x ⊢V⦂ A}
          → W ≐ᵛ W'
          --------------------------------------------------------
          → ⟨ y , f ⟩[ x ↦ W ]var ≐ᵛ ⟨ y , f' ⟩[ x ↦ W' ]var

sub-var-≐ y f f' x eW =
  cong₂ (λ g U → ⟨ y , g ⟩[ x ↦ U ]var) (bound-irr f f') eW

-- SUBSTITUTING INTO A RESOURCE VARIABLE
--
-- `⟨_⟩[_↦_]rvar` returns a variable and a grade bound; only the variable is
-- observable, and that is what an `unbox` node stores.

rvar-img : ∀ {Γ A B ρ σ τ}
         → ([ ρ ] B ∈[ σ ] Γ) → (x : A ∈[ τ ] Γ) → split-l x ⊢V⦂ A
         → Var (split-l x ++ᶜ split-r x) ([ ρ ] B)
rvar-img y x W = proj₁ (⟨ y ⟩[ x ↦ W ]rvar) , proj₁ (proj₂ (⟨ y ⟩[ x ↦ W ]rvar))

sub-rvar-≐ : ∀ {Γ A B ρ σ τ}
           → (y : [ ρ ] B ∈[ σ ] Γ) → (x : A ∈[ τ ] Γ)
           → {W W' : split-l x ⊢V⦂ A} → W ≐ᵛ W'
           ----------------------------------------
           → rvar-img y x W ≡ rvar-img y x W'

sub-rvar-≐ y x = cong (rvar-img y x)

-- RETYPING

substᵛ-≐ : ∀ {A Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {V V' : Γ₁ ⊢V⦂ A}
         → V ≐ᵛ V' → subst (_⊢V⦂ A) e V ≐ᵛ subst (_⊢V⦂ A) e V'
substᵛ-≐ {A} e = cong (subst (_⊢V⦂ A) e)

substᶜ-≐ : ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : Γ₁ ⊢C⦂ C}
         → M ≐ᶜ M' → subst (_⊢C⦂ C) e M ≐ᶜ subst (_⊢C⦂ C) e M'
substᶜ-≐ {C} e = cong (subst (_⊢C⦂ C) e)

substᶜ-≐′ : (f : Ctx → Ctx) → ∀ {C Γ₁ Γ₂} → (e : Γ₁ ≡ Γ₂) → {M M' : f Γ₁ ⊢C⦂ C}
          → M ≐ᶜ M'
          → subst (λ z → f z ⊢C⦂ C) e M ≐ᶜ subst (λ z → f z ⊢C⦂ C) e M'
substᶜ-≐′ f {C} e = cong (subst (λ z → f z ⊢C⦂ C) e)

------------------------------------------------------------------------
-- SUBSTITUTION IS A CONGRUENCE
------------------------------------------------------------------------

sub-≐ᵛ : ∀ {Γ A B ρ} → (x : A ∈[ ρ ] Γ) → {W W' : split-l x ⊢V⦂ A}
       → W ≐ᵛ W' → {V V' : Γ ⊢V⦂ B} → V ≐ᵛ V'
       → (V [ x ↦ W ]v) ≐ᵛ (V' [ x ↦ W' ]v)
sub-≐ᵛ x eW eV = cong₂ (λ U V₀ → V₀ [ x ↦ U ]v) eW eV

sub-≐ᶜ : ∀ {Γ A C ρ} → (x : A ∈[ ρ ] Γ) → {W W' : split-l x ⊢V⦂ A}
       → W ≐ᵛ W' → {M M' : Γ ⊢C⦂ C} → M ≐ᶜ M'
       → (M [ x ↦ W ]c) ≐ᶜ (M' [ x ↦ W' ]c)
sub-≐ᶜ x eW eM = cong₂ (λ U M₀ → M₀ [ x ↦ U ]c) eW eM

