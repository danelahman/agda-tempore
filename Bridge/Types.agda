------------------------------------------------------------------
-- Closed open types as types of the closed calculus            --
--                                                              --
-- An open type over the empty scope has no type variable, and  --
-- its grade expressions have values (`valʳ`, `valᵉ`). The      --
-- translations `⌞_⌟ᵛ`, `⌞_⌟ᶜ` and `⌞_⌟ᶜᵗˣ` are structural,     --
-- each grade expression going to its value; they identify      --
-- convertible expressions, so they are not injective. The      --
-- embeddings `⌜_⌝ᵛ`, `⌜_⌝ᶜ` and `⌜_⌝ᶜᵗˣ`, each grade going to  --
-- the constant expression, are sections of them.               --
------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module Bridge.Types (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types    S
open import Syntax.Contexts S

open import TypeInference.OpenSyntax.Grades    S
open import TypeInference.OpenSyntax.Types     S
open import TypeInference.OpenSyntax.Contexts  S
open import TypeInference.OpenSyntax.Subst     S
open import TypeInference.OpenSyntax.Instances S using (valʳ; valᵉ)

-- Translation

mutual

  ⌞_⌟ᵛ : OVType ∅ˢ → VType
  ⌞ tvar () ⌟ᵛ
  ⌞ Base b ⌟ᵛ     = Base b
  ⌞ Unit ⌟ᵛ       = Unit
  ⌞ Bool ⌟ᵛ       = Bool
  ⌞ Nat ⌟ᵛ        = Nat
  ⌞ A |×| B ⌟ᵛ    = ⌞ A ⌟ᵛ |×| ⌞ B ⌟ᵛ
  ⌞ A |+| B ⌟ᵛ    = ⌞ A ⌟ᵛ |+| ⌞ B ⌟ᵛ
  ⌞ |List| A ⌟ᵛ   = |List| ⌞ A ⌟ᵛ
  ⌞ Empty ⌟ᵛ      = Empty
  ⌞ A ⇒ C ⌟ᵛ      = ⌞ A ⌟ᵛ ⇒ ⌞ C ⌟ᶜ
  ⌞ [ ρ ] A ⌟ᵛ    = [ valʳ ρ ] ⌞ A ⌟ᵛ

  ⌞_⌟ᶜ : OCType ∅ˢ → CType
  ⌞ A ‼ ε ⌟ᶜ = ⌞ A ⌟ᵛ ‼ valᵉ ε

⌞_⌟ᶜᵗˣ : ∀ {n} → OCtx ∅ˢ n → Ctx
⌞ [] ⌟ᶜᵗˣ        = []
⌞ Γ ∷ A ⌟ᶜᵗˣ     = ⌞ Γ ⌟ᶜᵗˣ ∷ ⌞ A ⌟ᵛ
⌞ Γ ⟨ ρ ⟩ ⌟ᶜᵗˣ   = ⌞ Γ ⌟ᶜᵗˣ ⟨ valʳ ρ ⟩

-- Embedding

mutual

  ⌜_⌝ᵛ : VType → OVType ∅ˢ
  ⌜ Base b ⌝ᵛ     = Base b
  ⌜ Unit ⌝ᵛ       = Unit
  ⌜ Bool ⌝ᵛ       = Bool
  ⌜ Nat ⌝ᵛ        = Nat
  ⌜ A |×| B ⌝ᵛ    = ⌜ A ⌝ᵛ |×| ⌜ B ⌝ᵛ
  ⌜ A |+| B ⌝ᵛ    = ⌜ A ⌝ᵛ |+| ⌜ B ⌝ᵛ
  ⌜ |List| A ⌝ᵛ   = |List| ⌜ A ⌝ᵛ
  ⌜ Empty ⌝ᵛ      = Empty
  ⌜ A ⇒ C ⌝ᵛ      = ⌜ A ⌝ᵛ ⇒ ⌜ C ⌝ᶜ
  ⌜ [ ρ ] A ⌝ᵛ    = [ rconst ρ ] ⌜ A ⌝ᵛ

  ⌜_⌝ᶜ : CType → OCType ∅ˢ
  ⌜ A ‼ ε ⌝ᶜ = ⌜ A ⌝ᵛ ‼ econst ε

-- The number of variables a closed context binds

∣_∣ᶜ : Ctx → ℕ
∣ [] ∣ᶜ        = zero
∣ Γ ∷ A ∣ᶜ     = suc ∣ Γ ∣ᶜ
∣ Γ ⟨ ρ ⟩ ∣ᶜ   = ∣ Γ ∣ᶜ

⌜_⌝ᶜᵗˣ : (Γ : Ctx) → OCtx ∅ˢ ∣ Γ ∣ᶜ
⌜ [] ⌝ᶜᵗˣ      = []
⌜ Γ ∷ A ⌝ᶜᵗˣ   = ⌜ Γ ⌝ᶜᵗˣ ∷ ⌜ A ⌝ᵛ
⌜ Γ ⟨ ρ ⟩ ⌝ᶜᵗˣ = ⌜ Γ ⌝ᶜᵗˣ ⟨ rconst ρ ⟩

-- The embedding is a section of the translation

mutual

  ⌞⌜_⌝⌟ᵛ : (A : VType) → ⌞ ⌜ A ⌝ᵛ ⌟ᵛ ≡ A
  ⌞⌜ Base b ⌝⌟ᵛ   = refl
  ⌞⌜ Unit ⌝⌟ᵛ     = refl
  ⌞⌜ Bool ⌝⌟ᵛ     = refl
  ⌞⌜ Nat ⌝⌟ᵛ      = refl
  ⌞⌜ A |×| B ⌝⌟ᵛ  = cong₂ _|×|_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ B ⌝⌟ᵛ
  ⌞⌜ A |+| B ⌝⌟ᵛ  = cong₂ _|+|_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ B ⌝⌟ᵛ
  ⌞⌜ |List| A ⌝⌟ᵛ = cong |List| ⌞⌜ A ⌝⌟ᵛ
  ⌞⌜ Empty ⌝⌟ᵛ    = refl
  ⌞⌜ A ⇒ C ⌝⌟ᵛ    = cong₂ _⇒_ ⌞⌜ A ⌝⌟ᵛ ⌞⌜ C ⌝⌟ᶜ
  ⌞⌜ [ ρ ] A ⌝⌟ᵛ  = cong ([ ρ ]_) ⌞⌜ A ⌝⌟ᵛ

  ⌞⌜_⌝⌟ᶜ : (C : CType) → ⌞ ⌜ C ⌝ᶜ ⌟ᶜ ≡ C
  ⌞⌜ A ‼ ε ⌝⌟ᶜ = cong (_‼ ε) ⌞⌜ A ⌝⌟ᵛ

⌞⌜_⌝⌟ᶜᵗˣ : (Γ : Ctx) → ⌞ ⌜ Γ ⌝ᶜᵗˣ ⌟ᶜᵗˣ ≡ Γ
⌞⌜ [] ⌝⌟ᶜᵗˣ      = refl
⌞⌜ Γ ∷ A ⌝⌟ᶜᵗˣ   = cong₂ _∷_ ⌞⌜ Γ ⌝⌟ᶜᵗˣ ⌞⌜ A ⌝⌟ᵛ
⌞⌜ Γ ⟨ ρ ⟩ ⌝⌟ᶜᵗˣ = cong (_⟨ ρ ⟩) ⌞⌜ Γ ⌝⌟ᶜᵗˣ

-- Ground types translate to their closed images at every instance

⌞⌜_⌝ᵍ⌟ : ∀ {Θ} → (g : GType) → (δ : Subst Θ ∅ˢ) → ⌞ ⌜ g ⌝ᵍ [ δ ]ᵛ ⌟ᵛ ≡ type-of-gtype g
⌞⌜ Base b ⌝ᵍ⌟ δ     = refl
⌞⌜ Unit ⌝ᵍ⌟ δ       = refl
⌞⌜ Bool ⌝ᵍ⌟ δ       = refl
⌞⌜ Empty ⌝ᵍ⌟ δ      = refl
⌞⌜ A |×|ᵍ B ⌝ᵍ⌟ δ   = cong₂ _|×|_ (⌞⌜ A ⌝ᵍ⌟ δ) (⌞⌜ B ⌝ᵍ⌟ δ)
⌞⌜ [ ρ ]ᵍ A ⌝ᵍ⌟ δ   = cong ([ ρ ]_) (⌞⌜ A ⌝ᵍ⌟ δ)

-- An instance of the empty scope is the identity

∅-≐ˢ : (δ : Subst ∅ˢ ∅ˢ) → δ ≐ˢ idˢ
∅-≐ˢ δ = mk≐ˢ (λ ()) (λ ()) (λ ())

∅-[]ᵛ : (δ : Subst ∅ˢ ∅ˢ) → (A : OVType ∅ˢ) → A [ δ ]ᵛ ≡ A
∅-[]ᵛ δ A = trans ([≐]ᵛ (∅-≐ˢ δ) A) ([id]ᵛ A)

∅-[]ᶜ : (δ : Subst ∅ˢ ∅ˢ) → (C : OCType ∅ˢ) → C [ δ ]ᶜ ≡ C
∅-[]ᶜ δ C = trans ([≐]ᶜ (∅-≐ˢ δ) C) ([id]ᶜ C)

∅-[]ᶜᵗˣ : ∀ {n} → (δ : Subst ∅ˢ ∅ˢ) → (Γ : OCtx ∅ˢ n) → Γ [ δ ]ᶜᵗˣ ≡ Γ
∅-[]ᶜᵗˣ δ Γ = trans ([≐]ᶜᵗˣ (∅-≐ˢ δ) Γ) ([id]ᶜᵗˣ Γ)
