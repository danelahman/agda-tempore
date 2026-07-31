------------------------------------------------------------------------
-- Lemmas about the tick monad, shared by the top-level soundness proofs. --
--                                                                    --
-- Kleisli composition `_⋄ᵏ_`, its associativity, and `tick-nf`: binding  --
-- after a tick is a tick of the bound computation. `ImplLemmas` adds the --
-- one fact that holds of any implementation, namely that a graded monad  --
-- morphism maps a bind to a bind.                                       --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.Monad
open import DenotationalSemantics.Model.TickMonad

module OperationalSemantics.Soundness.TickLemmas
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (TMon : TickMonad S Cat Fut)
       where

open LanguageSpec S
open GradeSystemInterface Grades

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-∘ᵐ)
open Monad Mon using (Tᵒ; Tᶠ; μᵀ)
open TickMonad TMon

-- Chaining equational steps.

infixr 3 _∙ᵏ_

_∙ᵏ_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙ᵏ_ = ≈ᵐ-trans

-- Kleisli composition with a time transition: running a computation over the
-- later history, after the transition producing it. The grades multiply.

infixl 25 _⋄ᵏ_

_⋄ᵏ_ : ∀ {X Y A ε ε'} → (Y →ᵐ Tᵏ A ε') → (X →ᵐ Tᵏ Y ε) → X →ᵐ Tᵏ A (ε ·ₑ ε')
f ⋄ᵏ t = μᵏ ∘ᵐ Tᵏᶠ f ∘ᵐ t

⋄ᵏ-ηᵏ : ∀ {X A ε'} → (f : X →ᵐ Tᵏ A ε')
      → f ⋄ᵏ ηᵏ ≈ᵐ ε-substᵏ (sym (·ₑ-identityˡ ε')) ∘ᵐ f
⋄ᵏ-ηᵏ f =
    ∘ᵐ-congʳ (≈ᵐ-sym (ηᵏ-nat f))
  ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congˡ Tᵏ-μ∘η≡id

-- The Kleisli composite is associative.

bind-bindᵏ : ∀ {X Y Z B ε₁ ε₂ ε₃}
           → (f : Z →ᵐ Tᵏ B ε₃) → (t : Y →ᵐ Tᵏ Z ε₂) → (s : X →ᵐ Tᵏ Y ε₁)
           → μᵏ ∘ᵐ Tᵏᶠ (f ⋄ᵏ t) ∘ᵐ s
           ≈ᵐ ε-substᵏ (·ₑ-assoc ε₁ ε₂ ε₃) ∘ᵐ (f ⋄ᵏ (t ⋄ᵏ s))
bind-bindᵏ f t s =
    ∘ᵐ-congʳ (∘ᵐ-congˡ (Tᵏ-∘ᵐ _ _ ∙ᵏ ∘ᵐ-congʳ (Tᵏ-∘ᵐ _ _)))
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ᵏ ∘ᵐ-congˡ (∘ᵐ-congˡ Tᵏ-μ∘μ≡μ∘Tμ)
  ∙ᵏ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ᵏ ∘ᵐ-congˡ (∘ᵐ-congʳ (∘ᵐ-congʳ (μᵏ-nat f)))
  ∙ᵏ ∘ᵐ-assoc _ _ _
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))

-- BINDING AFTER A TICK
--
-- A tick is natural and algebraic, so the bind goes under it, and the
-- transition's `ηᵏ` is absorbed, leaving only a regrading.

tick-z : ∀ (δ : E) (ε : E) → δ ·ₑ ε ≾ₑ (δ ·ₑ uₑ) ·ₑ ε
tick-z δ ε =
  ≾ₑ-trans (·ₑ-monoʳ-≾ₑ (≾ₑ-reflexive (sym (·ₑ-identityˡ ε))))
           (≾ₑ-reflexive (sym (·ₑ-assoc δ uₑ ε)))

tick-nf : ∀ {X Y B ε} → (δ : E) → (env : X →ᵐ [ mapᵉ δ ]ᵒ Y)
        → (f : Y →ᵐ Tᵏ B ε)
        → μᵏ ∘ᵐ Tᵏᶠ f ∘ᵐ (tickᵏ δ ∘ᵐ [ mapᵉ δ ]ᶠ ηᵏ ∘ᵐ env)
        ≈ᵐ T-≤ᵏ (tick-z δ ε) ∘ᵐ tickᵏ δ ∘ᵐ [ mapᵉ δ ]ᶠ f ∘ᵐ env
tick-nf {ε = ε} δ env f =
    ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (tickᵏ-nat δ f)))
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congˡ (tickᵏ-algebraicity δ)
  ∙ᵏ ∘ᵐ-assoc _ _ _
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ
      (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ᵏ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
       ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
       ∙ᵏ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
       ∙ᵏ ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-assoc _ _ _ ∙ᵏ ⋄ᵏ-ηᵏ f ∙ᵏ ∘ᵐ-congˡ (T-≤ᵏ-≡ _)))
       ∙ᵏ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
       ∙ᵏ ∘ᵐ-assoc _ _ _))
  ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (tickᵏ-≤ δ _))
  ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ᵏ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᵏ ∘ᵐ-congˡ (∘ᵐ-congˡ (T-≤ᵏ-≡ _) ∙ᵏ T-≤ᵏ-trans _ _ (tick-z δ ε))

-- Being a graded monad morphism, an implementation maps a bind to a bind. This
-- is what carries the tree monad's soundness theorem over to `↝-STEP`.

module ImplLemmas
         (implᵐ : ∀ {A ε} → Tᵒ A ε →ᵐ Tᵏ A ε)
         (implᵐ-μᵀ : ∀ {A ε ε'}
                   → implᵐ ∘ᵐ μᵀ {A} {ε} {ε'} ≈ᵐ μᵏ ∘ᵐ Tᵏᶠ implᵐ ∘ᵐ implᵐ)
         (implᵐ-nat : ∀ {A B ε} → (f : A →ᵐ B)
                    → implᵐ {ε = ε} ∘ᵐ Tᶠ f ≈ᵐ Tᵏᶠ f ∘ᵐ implᵐ)
       where

  impl-⋄ : ∀ {X Y A ε ε'} → (f : Y →ᵐ Tᵒ A ε') → (t : X →ᵐ Tᵒ Y ε)
         → implᵐ ∘ᵐ (μᵀ ∘ᵐ Tᶠ f ∘ᵐ t)
         ≈ᵐ (implᵐ ∘ᵐ f) ⋄ᵏ (implᵐ ∘ᵐ t)
  impl-⋄ f t =
      ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ᵏ ∘ᵐ-congˡ implᵐ-μᵀ
    ∙ᵏ ∘ᵐ-assoc _ _ _
    ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
    ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
    ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (implᵐ-nat f)))
    ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    ∙ᵏ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    ∙ᵏ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (Tᵏ-∘ᵐ _ _)))
