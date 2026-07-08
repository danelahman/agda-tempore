------------------------------------------------------------------------
-- Semantics of the box modality `[ ρ ] A` on types, as a functor      --
-- graded by a monoid of grades `(R , · , u , ≾)`. It is the analogue  --
-- of the comonadic □-modality on types in Fitch-style modal calculi.  --
--                                                                    --
-- The modality is a *lax* graded comonad: it provides a counit `ε`    --
-- and comultiplication `δ`, but no inverses. (With expiring resources --
-- the box is genuinely lax — a smaller resource budget is a strictly  --
-- stronger obligation, so `[ ρ₁ · ρ₂ ]` and `[ ρ₁ ] [ ρ₂ ]` need not  --
-- coincide.) Laws are stated up to propositional equality `≡`, and,    --
-- because the monoid laws hold only propositionally, the graded        --
-- comonad laws carry explicit `[]-≤` coercions along `·-identityˡ`,    --
-- `·-identityʳ`, and `·-assoc`.                                        --
------------------------------------------------------------------------

open import Syntax.Grades

open import DenotationalSemantics.Model.Category

module DenotationalSemantics.Model.Modality.Future (Cat : Category) (G : Grade) where

open import Util.Equality

open Category Cat
open Grade G

-- two-sided monotonicity of `·` derived from the one-sided ones

·-mono-≾ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≾ ρ₁' → ρ₂ ≾ ρ₂' → ρ₁ · ρ₂ ≾ ρ₁' · ρ₂'
·-mono-≾ p q = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ q)

record Future : Set₁ where

  field

    -- STRUCTURE

    -- Functor

    [_]ᵒ : Carrier → Obj → Obj
    [_]ᶠ : ∀ {A B} → (ρ : Carrier) → A →ᵐ B → [ ρ ]ᵒ A →ᵐ [ ρ ]ᵒ B

    -- Monotonicity for gradings. The box is `∀`-shaped (Kripke
    -- necessity), so it is *contravariant* in the grade: a larger grade
    -- (a larger accessibility relation) is a stronger obligation.

    []-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → [ ρ₂ ]ᵒ A →ᵐ [ ρ₁ ]ᵒ A

    -- Counit

    ε : ∀ {A} → [ u ]ᵒ A →ᵐ A

    -- Comultiplication

    δ : ∀ {A ρ₁ ρ₂} → [ ρ₁ · ρ₂ ]ᵒ A →ᵐ [ ρ₁ ]ᵒ ([ ρ₂ ]ᵒ A)

    -- Monoidality (lax): a boxed `A` and a boxed `B` at the same grade
    -- combine into a boxed pair. This is what lets the monad's strength
    -- distribute the box over a product in the associativity and the
    -- operations-wrt-strength laws.

    []-monoidal : ∀ {A B ρ} → [ ρ ]ᵒ A ×ᵐ [ ρ ]ᵒ B →ᵐ [ ρ ]ᵒ (A ×ᵐ B)

    -- PROPERTIES

    -- [_] is functorial

    []-idᵐ : ∀ {A ρ} → [ ρ ]ᶠ (idᵐ {A = A}) ≡ idᵐ
    []-∘ᵐ : ∀ {A B C ρ} → (f : A →ᵐ B) → (g : B →ᵐ C)
          → [ ρ ]ᶠ (g ∘ᵐ f) ≡ [ ρ ]ᶠ g ∘ᵐ [ ρ ]ᶠ f

    -- []-≤ is natural

    []-≤-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵐ B) → (p : ρ₁ ≾ ρ₂)
             → [ ρ₁ ]ᶠ f ∘ᵐ []-≤ {A = A} p ≡ []-≤ {A = B} p ∘ᵐ [ ρ₂ ]ᶠ f

    -- [_] is functorial in the gradings

    []-≤-refl : ∀ {A ρ} → []-≤ {A} (≾-refl {ρ}) ≡ idᵐ
    []-≤-trans : ∀ {A ρ ρ' ρ''} → (p : ρ ≾ ρ') → (q : ρ' ≾ ρ'')
               → []-≤ {A} p ∘ᵐ []-≤ {A} q ≡ []-≤ {A} (≾-trans p q)

    -- ε is natural

    []-ε-nat : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ ε ≡ ε ∘ᵐ [ u ]ᶠ f

    -- δ is natural

    []-δ-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵐ B)
             → [ ρ₁ ]ᶠ ([ ρ₂ ]ᶠ f) ∘ᵐ δ {A} ≡ δ {B} ∘ᵐ [ ρ₁ · ρ₂ ]ᶠ f

    -- []-monoidal is natural

    []-monoidal-nat : ∀ {A B C D ρ} → (f : A →ᵐ C) → (g : B →ᵐ D)
                    → [ ρ ]ᶠ (mapˣᵐ f g) ∘ᵐ []-monoidal
                    ≡ []-monoidal ∘ᵐ mapˣᵐ ([ ρ ]ᶠ f) ([ ρ ]ᶠ g)

    -- δ is compatible with the gradings

    []-δ-≤ : ∀ {A ρ₁ ρ₂ ρ₁' ρ₂'} → (p : ρ₁ ≾ ρ₁') → (q : ρ₂ ≾ ρ₂')
           → []-≤ {[ ρ₂ ]ᵒ A} p ∘ᵐ [ ρ₁' ]ᶠ ([]-≤ {A} q) ∘ᵐ δ {A} {ρ₁'} {ρ₂'}
           ≡ δ {A} {ρ₁} {ρ₂} ∘ᵐ []-≤ {A} (·-mono-≾ p q)

    -- Graded comonad laws

    []-ε∘δ≡id : ∀ {A ρ}
              → ε {[ ρ ]ᵒ A} ∘ᵐ δ {A} {u} {ρ}
              ≡ []-≤ {A = A} (≾-reflexive (sym (·-identityˡ ρ)))
    []-Dε∘δ≡id : ∀ {A ρ}
               → [ ρ ]ᶠ (ε {A}) ∘ᵐ δ {A} {ρ} {u}
               ≡ []-≤ {A} (≾-reflexive (sym (·-identityʳ ρ)))
    []-δ∘δ≡Dδ∘δ : ∀ {A ρ₁ ρ₂ ρ₃}
                → δ {[ ρ₃ ]ᵒ A} {ρ₁} {ρ₂} ∘ᵐ δ {A} {ρ₁ · ρ₂} {ρ₃}
                ≡    [ ρ₁ ]ᶠ (δ {A} {ρ₂} {ρ₃}) ∘ᵐ δ {A} {ρ₁} {ρ₂ · ρ₃}
                  ∘ᵐ []-≤ {A} (≾-reflexive (sym (·-assoc ρ₁ ρ₂ ρ₃)))
