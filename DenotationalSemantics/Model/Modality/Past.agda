------------------------------------------------------------------------
-- Semantics of the context modality `Γ ⟨ ρ ⟩`, as a functor graded by --
-- a monoid of grades `(R , · , u , ≾)`. It is the analogue of the      --
-- monadic lock-modality on contexts in Fitch-style modal calculi.      --
--                                                                    --
-- The modality is a *lax* graded monad: unit `η` and multiplication   --
-- `μ`. Concretely it is realised as Kripke possibility (a Σ-type over  --
-- accessible *past* worlds). Laws are stated up to the categorical     --
-- equality `≈ᵐ`.                                                        --
--                                                                    --
-- At the *unit* resource grade the unit is additionally an             --
-- isomorphism: a unit-graded counit `εᵘ : ⟨ u ⟩ᵒ A →ᵐ A` splits `η`,   --
-- so `⟨ u ⟩ᵒ A ≅ A`. This is dual to the box modality's unit-graded    --
-- unit `ηᵘ`, and combined with the graded adjunction `⟨ ρ ⟩ ⊣ [ ρ ]`   --
-- it is what interprets using a variable once the resources to its     --
-- right sum to the unit grade.                                         --
--                                                                    --
-- Note on the grade order: `μ` reverses the multiplication order,     --
--   μ : ⟨ ρ₁ ⟩ (⟨ ρ₂ ⟩ A) →ᵐ ⟨ ρ₂ · ρ₁ ⟩ A ,                          --
-- so that, under `⟦ Γ ⟨ ρ ⟩ ⟧ = ⟨ ρ ⟩ ⟦ Γ ⟧`, folding a nested       --
-- context `Γ ⟨ ρ₁ ⟩ ⟨ ρ₂ ⟩` yields the grade `ρ₁ · ρ₂`, matching      --
-- `ctx-grade (Γ ⟨ ρ₁ ⟩ ⟨ ρ₂ ⟩) = (… · ρ₁) · ρ₂` of the calculus.      --
------------------------------------------------------------------------

open import Syntax.Grades

open import DenotationalSemantics.Model.Category

module DenotationalSemantics.Model.Modality.Past (Cat : Category) (G : Grade) where

open import Util.Equality

open Category Cat
open Grade G

-- two-sided monotonicity of `·` derived from the one-sided ones

·-mono-≾ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≾ ρ₁' → ρ₂ ≾ ρ₂' → ρ₁ · ρ₂ ≾ ρ₁' · ρ₂'
·-mono-≾ p q = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ q)

record Past : Set₁ where

  field

    -- STRUCTURE

    -- Functor

    ⟨_⟩ᵒ : Carrier → Obj → Obj
    ⟨_⟩ᶠ : ∀ {A B} → (ρ : Carrier) → A →ᵐ B → ⟨ ρ ⟩ᵒ A →ᵐ ⟨ ρ ⟩ᵒ B

    -- Monotonicity for gradings. The context modality is `Σ`-shaped
    -- (Kripke possibility), so it is *covariant* in the grade.

    ⟨⟩-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → ⟨ ρ₁ ⟩ᵒ A →ᵐ ⟨ ρ₂ ⟩ᵒ A

    -- Unit

    η : ∀ {A} → A →ᵐ ⟨ u ⟩ᵒ A

    -- Multiplication (note the reversed grade order, see the header)

    μ : ∀ {A ρ₁ ρ₂} → ⟨ ρ₁ ⟩ᵒ (⟨ ρ₂ ⟩ᵒ A) →ᵐ ⟨ ρ₂ · ρ₁ ⟩ᵒ A

    -- Unit-graded counit: the inverse of the unit `η` at grade `u`.

    εᵘ : ∀ {A} → ⟨ u ⟩ᵒ A →ᵐ A

    -- PROPERTIES

    -- ⟨_⟩ is functorial

    ⟨⟩-idᵐ : ∀ {A ρ} → ⟨ ρ ⟩ᶠ (idᵐ {A = A}) ≈ᵐ idᵐ
    ⟨⟩-∘ᵐ : ∀ {A B C ρ} → (g : B →ᵐ C) → (f : A →ᵐ B)
          → ⟨ ρ ⟩ᶠ (g ∘ᵐ f) ≈ᵐ ⟨ ρ ⟩ᶠ g ∘ᵐ ⟨ ρ ⟩ᶠ f

    -- ⟨_⟩ᶠ is a congruence

    ⟨⟩-congᶠ : ∀ {A B ρ} {f g : A →ᵐ B} → f ≈ᵐ g → ⟨ ρ ⟩ᶠ f ≈ᵐ ⟨ ρ ⟩ᶠ g

    -- ⟨⟩-≤ is natural

    ⟨⟩-≤-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵐ B) → (p : ρ₁ ≾ ρ₂)
             → ⟨ ρ₂ ⟩ᶠ f ∘ᵐ ⟨⟩-≤ p ≈ᵐ ⟨⟩-≤ p ∘ᵐ ⟨ ρ₁ ⟩ᶠ f

    -- ⟨_⟩ is functorial in the gradings

    ⟨⟩-≤-refl : ∀ {A ρ} → ⟨⟩-≤ {A} (≾-refl {ρ}) ≈ᵐ idᵐ
    ⟨⟩-≤-trans : ∀ {A ρ ρ' ρ''} → (p : ρ ≾ ρ') → (q : ρ' ≾ ρ'')
               → ⟨⟩-≤ {A} q ∘ᵐ ⟨⟩-≤ {A} p ≈ᵐ ⟨⟩-≤ (≾-trans p q)

    -- η is natural

    ⟨⟩-η-nat : ∀ {A B} → (f : A →ᵐ B) → ⟨ u ⟩ᶠ f ∘ᵐ η ≈ᵐ η ∘ᵐ f

    -- μ is natural

    ⟨⟩-μ-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵐ B)
             → ⟨ ρ₂ · ρ₁ ⟩ᶠ f ∘ᵐ μ ≈ᵐ μ ∘ᵐ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ f)

    -- μ is compatible with the gradings

    ⟨⟩-μ-≤ : ∀ {A ρ₁ ρ₂ ρ₁' ρ₂'} → (p : ρ₁ ≾ ρ₁') → (q : ρ₂ ≾ ρ₂')
           → ⟨⟩-≤ {A} (·-mono-≾ q p) ∘ᵐ μ {A} {ρ₁} {ρ₂}
           ≈ᵐ μ {A} {ρ₁'} {ρ₂'} ∘ᵐ ⟨ ρ₁' ⟩ᶠ (⟨⟩-≤ q) ∘ᵐ ⟨⟩-≤ p

    -- Graded monad laws

    ⟨⟩-μ∘η≡id : ∀ {A ρ}
              → μ {A} {u} {ρ} ∘ᵐ η
              ≈ᵐ ⟨⟩-≤ (≾-reflexive (sym (·-identityʳ ρ)))
    ⟨⟩-μ∘Tη≡id : ∀ {A ρ}
               → μ {A} {ρ} {u} ∘ᵐ ⟨ ρ ⟩ᶠ η
               ≈ᵐ ⟨⟩-≤ (≾-reflexive (sym (·-identityˡ ρ)))
    ⟨⟩-μ∘μ≡μ∘Tμ : ∀ {A ρ₁ ρ₂ ρ₃}
                → μ {A} {ρ₂ · ρ₁} {ρ₃} ∘ᵐ μ {⟨ ρ₃ ⟩ᵒ A} {ρ₁} {ρ₂}
                ≈ᵐ    ⟨⟩-≤ (≾-reflexive (·-assoc ρ₃ ρ₂ ρ₁))
                  ∘ᵐ μ {A} {ρ₁} {ρ₃ · ρ₂} ∘ᵐ ⟨ ρ₁ ⟩ᶠ (μ {A} {ρ₂} {ρ₃})

    -- εᵘ is natural

    εᵘ-nat : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ εᵘ ≈ᵐ εᵘ ∘ᵐ ⟨ u ⟩ᶠ f

    -- εᵘ and the unit η are mutually inverse (so `⟨ u ⟩ᵒ A ≅ A`)

    ⟨⟩-εᵘ∘η≡id : ∀ {A} → εᵘ {A} ∘ᵐ η {A} ≈ᵐ idᵐ
    ⟨⟩-η∘εᵘ≡id : ∀ {A} → η {A} ∘ᵐ εᵘ {A} ≈ᵐ idᵐ
