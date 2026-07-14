------------------------------------------------------------------------
-- Runtime computations of morphisms, and the Kleisli maps they induce.  --
--                                                                    --
-- A term `Γ ⊢C⦂ C` denotes a morphism `⟦Γ⟧ →ᵐ ⟦C⟧`, i.e. a *point* of   --
-- the exponential, `𝟙ᵐ →ᵐ (⟦Γ⟧ ⇒ᵐ ⟦C⟧)` (`ptᵐ`). So a runtime            --
-- computation of terms denotes a point of `Mᵒ (⟦Γ⟧ ⇒ᵐ ⟦C⟧)`.            --
--                                                                    --
-- `kleisliᵐ` turns such a point back into a Kleisli map `⟦Γ⟧ →ᵐ Mᵒ ⟦C⟧`  --
-- by feeding it the environment through the strength and applying, and    --
-- `kleisliᵐ-ptᵐ` says it takes a returned morphism to itself.             --
------------------------------------------------------------------------

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.RuntimeMonad

module DenotationalSemantics.Soundness.RuntimeLemmas
         (Cat : Category)
         (RMon : RuntimeMonad Cat)
       where

open Category Cat
open RuntimeMonad RMon

infixr 3 _∙ᴹ_

_∙ᴹ_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙ᴹ_ = ≈ᵐ-trans

swapᵐ : ∀ {A B} → A ×ᵐ B →ᵐ B ×ᵐ A
swapᵐ = ⟨ sndᵐ , fstᵐ ⟩ᵐ

-- The point of the exponential naming a morphism.

ptᵐ : ∀ {X Y} → (X →ᵐ Y) → (𝟙ᵐ →ᵐ (X ⇒ᵐ Y))
ptᵐ f = curryᵐ (f ∘ᵐ sndᵐ)

-- The Kleisli map a runtime computation of points induces.

kleisliᵐ : ∀ {X Y} → (𝟙ᵐ →ᵐ Mᵒ (X ⇒ᵐ Y)) → (X →ᵐ Mᵒ Y)
kleisliᵐ b = Mᶠ (appᵐ ∘ᵐ swapᵐ) ∘ᵐ strᴹ ∘ᵐ ⟨ idᵐ , b ∘ᵐ terminalᵐ ⟩ᵐ

kleisliᵐ-cong : ∀ {X Y} → {b b' : 𝟙ᵐ →ᵐ Mᵒ (X ⇒ᵐ Y)}
              → b ≈ᵐ b' → kleisliᵐ b ≈ᵐ kleisliᵐ b'
kleisliᵐ-cong e =
  ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-congˡ e ⟩ᵐ-cong))

-- The functorial action of the product, on a pairing.

mapˣᵐ-⟨,⟩ʳ : ∀ {H X D D'} → (h : D →ᵐ D') → (f : H →ᵐ X) → (c : H →ᵐ D)
           → mapˣᵐ idᵐ h ∘ᵐ ⟨ f , c ⟩ᵐ ≈ᵐ ⟨ f , h ∘ᵐ c ⟩ᵐ
mapˣᵐ-⟨,⟩ʳ h f c =
    mapˣᵐ-∘⟨⟩ idᵐ h f c
  ∙ᴹ ⟨ ∘ᵐ-identityˡ f , ≈ᵐ-refl ⟩ᵐ-cong

-- A returned morphism induces itself.

kleisliᵐ-ptᵐ : ∀ {X Y} → (f : X →ᵐ Y)
             → kleisliᵐ (ηᴹ ∘ᵐ ptᵐ f) ≈ᵐ ηᴹ ∘ᵐ f
kleisliᵐ-ptᵐ f =
    -- the runtime unit passes through the strength …
    ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong))
  ∙ᴹ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-⟨,⟩ʳ ηᴹ idᵐ _)))
  ∙ᴹ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ᴹ ∘ᵐ-congʳ (∘ᵐ-congˡ strᴹ-ηᴹ)
  ∙ᴹ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ᴹ ∘ᵐ-congˡ (ηᴹ-nat _)
  ∙ᴹ ∘ᵐ-assoc _ _ _
    -- … and what is left is a beta reduction
  ∙ᴹ ∘ᵐ-congʳ beta
  where
    beta : (appᵐ ∘ᵐ swapᵐ) ∘ᵐ ⟨ idᵐ , ptᵐ f ∘ᵐ terminalᵐ ⟩ᵐ ≈ᵐ f
    beta =
        ∘ᵐ-assoc _ _ _
      ∙ᴹ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                   ∙ᴹ ⟨ ⟨⟩ᵐ-sndᵐ _ _ , ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong)
      ∙ᴹ ∘ᵐ-congʳ (⟨ ≈ᵐ-sym (curryᵐ-nat terminalᵐ (f ∘ᵐ sndᵐ)) , ≈ᵐ-refl ⟩ᵐ-cong)
      ∙ᴹ βᵐ _ _
      ∙ᴹ ∘ᵐ-assoc _ _ _
      ∙ᴹ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                   ∙ᴹ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong)
      ∙ᴹ ∘ᵐ-assoc _ _ _
      ∙ᴹ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
      ∙ᴹ ∘ᵐ-identityʳ _
