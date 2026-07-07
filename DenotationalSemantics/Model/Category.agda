------------------------------------------------------------------------
-- Core category structure for the models of the language.             --
--                                                                    --
-- Morphism equality is plain propositional equality `≡`. Both          --
-- modalities are ordinary Kripke (co)limits over a *discrete* presheaf  --
-- category, so their morphism equalities are propositional (provable    --
-- from function extensionality), and `≡` suffices.                      --
--                                                                    --
-- Only the *core* structure (identities, composition) is recorded, as  --
-- that is all the box and context modalities require. The cartesian    --
-- closed structure is added on top when interpreting the types.        --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Category where

open import Util.Equality

record Category : Set₂ where

  -- OBJECTS AND MORPHISMS

  field
    Obj : Set₁

    _→ᵐ_ : (A B : Obj) → Set₀

  infix 20 _→ᵐ_

  -- IDENTITIES AND COMPOSITION

  field
    idᵐ : ∀ {A} → A →ᵐ A
    _∘ᵐ_ : ∀ {A B C} → B →ᵐ C → A →ᵐ B → A →ᵐ C

    ∘ᵐ-identityˡ : ∀ {A B} → (f : A →ᵐ B) → idᵐ ∘ᵐ f ≡ f
    ∘ᵐ-identityʳ : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ idᵐ ≡ f
    ∘ᵐ-assoc : ∀ {A B C D} → (h : C →ᵐ D) → (g : B →ᵐ C) → (f : A →ᵐ B)
             → (h ∘ᵐ g) ∘ᵐ f ≡ h ∘ᵐ (g ∘ᵐ f)

  infixr 9 _∘ᵐ_
