------------------------------------------------------------------------
-- The RUNTIME MONAD, semantically: the model's counterpart of the monad  --
-- the monadic top-level operational semantics implements its operations  --
-- in. That one is a monad on `Set`, over the syntax; this is a strong    --
-- monad `Mᵒ` on the model category, over the denotations.                --
--                                                                    --
-- It is not graded and has no ticks. It accounts for whatever the        --
-- external implementations do besides returning a value (fail, diverge,  --
-- choose, write), and knows nothing of the language's effects or         --
-- resources.                                                            --
--                                                                    --
-- The strength is what lets an operation's continuation be run under it: --
-- the environment sits beside the `Mᵒ`-computation the implementation    --
-- produces, and has to be carried into it.                               --
------------------------------------------------------------------------

open import Util.Equality

open import DenotationalSemantics.Model.Category

module DenotationalSemantics.Model.RuntimeMonad (Cat : Category) where

open Category Cat

record RuntimeMonad : Set₁ where

  field

    -- THE MONAD

    Mᵒ : Obj → Obj
    Mᶠ : ∀ {A B} → A →ᵐ B → Mᵒ A →ᵐ Mᵒ B
    ηᴹ : ∀ {A} → A →ᵐ Mᵒ A
    μᴹ : ∀ {A} → Mᵒ (Mᵒ A) →ᵐ Mᵒ A

    Mᶠ-idᵐ  : ∀ {A} → Mᶠ (idᵐ {A}) ≈ᵐ idᵐ
    Mᶠ-∘ᵐ   : ∀ {A B C} → (g : B →ᵐ C) → (f : A →ᵐ B)
            → Mᶠ (g ∘ᵐ f) ≈ᵐ Mᶠ g ∘ᵐ Mᶠ f
    Mᶠ-cong : ∀ {A B} → {f g : A →ᵐ B} → f ≈ᵐ g → Mᶠ f ≈ᵐ Mᶠ g

    ηᴹ-nat : ∀ {A B} → (f : A →ᵐ B) → Mᶠ f ∘ᵐ ηᴹ ≈ᵐ ηᴹ ∘ᵐ f
    μᴹ-nat : ∀ {A B} → (f : A →ᵐ B) → Mᶠ f ∘ᵐ μᴹ ≈ᵐ μᴹ ∘ᵐ Mᶠ (Mᶠ f)

    M-μ∘η≡id  : ∀ {A} → μᴹ {A} ∘ᵐ ηᴹ ≈ᵐ idᵐ
    M-μ∘Mη≡id : ∀ {A} → μᴹ {A} ∘ᵐ Mᶠ ηᴹ ≈ᵐ idᵐ
    M-μ∘μ≡μ∘Mμ : ∀ {A} → μᴹ {A} ∘ᵐ μᴹ ≈ᵐ μᴹ ∘ᵐ Mᶠ μᴹ

    -- THE STRENGTH

    strᴹ : ∀ {A B} → (A ×ᵐ Mᵒ B) →ᵐ Mᵒ (A ×ᵐ B)

    strᴹ-nat : ∀ {A B C D} → (f : A →ᵐ C) → (g : B →ᵐ D)
             → strᴹ ∘ᵐ mapˣᵐ f (Mᶠ g) ≈ᵐ Mᶠ (mapˣᵐ f g) ∘ᵐ strᴹ
    strᴹ-ηᴹ  : ∀ {A B} → strᴹ {A} {B} ∘ᵐ mapˣᵐ idᵐ ηᴹ ≈ᵐ ηᴹ
    strᴹ-μᴹ  : ∀ {A B} → strᴹ {A} {B} ∘ᵐ mapˣᵐ idᵐ μᴹ
             ≈ᵐ μᴹ ∘ᵐ Mᶠ strᴹ ∘ᵐ strᴹ
