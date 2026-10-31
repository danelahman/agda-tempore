--------------------------------------------------------------------------
-- Semantics of the box modality `[ ρ ] A` on types, as a functor       --
-- graded by a monoid of grades `(R , · , u , ≾)`. It is the analogue   --
-- of the comonadic □-modality on types in Fitch-style modal calculi.   --
--                                                                      --
-- The modality is a lax graded comonad, with counit `ε` and            --
-- comultiplication `δ`. (With expiring resources the box is            --
-- genuinely lax: a smaller resource budget is a strictly stronger      --
-- obligation, so `[ ρ₁ · ρ₂ ]` and `[ ρ₁ ] [ ρ₂ ]` need not coincide.) --
-- Laws are stated up to the categorical equality `≈ᵐ`, and, because    --
-- the monoid laws hold only propositionally, the graded comonad laws   --
-- carry explicit `[]-≤` coercions along `·-identityˡ`, `·-identityʳ`,  --
-- and `·-assoc`.                                                       --
--                                                                      --
-- At the unit resource grade the counit is moreover an                 --
-- isomorphism: a unit-graded unit `ηᵘ : A →ᵐ [ u ]ᵒ A` splits `ε`, so  --
-- `[ u ]ᵒ A ≅ A`. This is the semantic counterpart of the calculus     --
-- being able to use a variable once the resources to its right sum to  --
-- the unit grade, and it is dual to the context modality's             --
-- unit-graded counit `εᵘ`.                                             --
--------------------------------------------------------------------------

open import Grades.Durations using (Duration)
open import Grades.Base

open import MonomorphicCalculus.DenotationalSemantics.Model.Category

module MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future (Cat : Category) {D : Duration} (G : Grade D) where

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
    -- necessity), so it is contravariant in the grade: a larger grade
    -- (a larger accessibility relation) is a stronger obligation.

    []-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → [ ρ₂ ]ᵒ A →ᵐ [ ρ₁ ]ᵒ A

    -- Counit

    ε : ∀ {A} → [ u ]ᵒ A →ᵐ A

    -- Comultiplication

    δ : ∀ {A ρ₁ ρ₂} → [ ρ₁ · ρ₂ ]ᵒ A →ᵐ [ ρ₁ ]ᵒ ([ ρ₂ ]ᵒ A)

    -- Unit-graded unit: the inverse of the counit `ε` at grade `u`.

    ηᵘ : ∀ {A} → A →ᵐ [ u ]ᵒ A

    -- Monoidality (lax): a boxed `A` and a boxed `B` at the same grade
    -- combine into a boxed pair. This is what lets the monad's strength
    -- distribute the box over a product in the associativity and the
    -- operations-wrt-strength laws.

    []-monoidal : ∀ {A B ρ} → [ ρ ]ᵒ A ×ᵐ [ ρ ]ᵒ B →ᵐ [ ρ ]ᵒ (A ×ᵐ B)

    -- PROPERTIES

    -- [_] is functorial

    []-idᵐ : ∀ {A ρ} → [ ρ ]ᶠ (idᵐ {A = A}) ≈ᵐ idᵐ
    []-∘ᵐ : ∀ {A B C ρ} → (f : A →ᵐ B) → (g : B →ᵐ C)
          → [ ρ ]ᶠ (g ∘ᵐ f) ≈ᵐ [ ρ ]ᶠ g ∘ᵐ [ ρ ]ᶠ f

    -- [_]ᶠ is a congruence

    []-congᶠ : ∀ {A B ρ} {f g : A →ᵐ B} → f ≈ᵐ g → [ ρ ]ᶠ f ≈ᵐ [ ρ ]ᶠ g

    -- []-≤ is natural

    []-≤-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵐ B) → (p : ρ₁ ≾ ρ₂)
             → [ ρ₁ ]ᶠ f ∘ᵐ []-≤ {A = A} p ≈ᵐ []-≤ {A = B} p ∘ᵐ [ ρ₂ ]ᶠ f

    -- [_] is functorial in the gradings

    []-≤-refl : ∀ {A ρ} → []-≤ {A} (≾-refl {ρ}) ≈ᵐ idᵐ
    []-≤-trans : ∀ {A ρ ρ' ρ''} → (p : ρ ≾ ρ') → (q : ρ' ≾ ρ'')
               → []-≤ {A} p ∘ᵐ []-≤ {A} q ≈ᵐ []-≤ {A} (≾-trans p q)

    -- ε is natural

    []-ε-nat : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ ε ≈ᵐ ε ∘ᵐ [ u ]ᶠ f

    -- δ is natural

    []-δ-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵐ B)
             → [ ρ₁ ]ᶠ ([ ρ₂ ]ᶠ f) ∘ᵐ δ {A} ≈ᵐ δ {B} ∘ᵐ [ ρ₁ · ρ₂ ]ᶠ f

    -- []-monoidal is natural

    []-monoidal-nat : ∀ {A B C D ρ} → (f : A →ᵐ C) → (g : B →ᵐ D)
                    → [ ρ ]ᶠ (mapˣᵐ f g) ∘ᵐ []-monoidal
                    ≈ᵐ []-monoidal ∘ᵐ mapˣᵐ ([ ρ ]ᶠ f) ([ ρ ]ᶠ g)

    -- δ is compatible with the gradings

    []-δ-≤ : ∀ {A ρ₁ ρ₂ ρ₁' ρ₂'} → (p : ρ₁ ≾ ρ₁') → (q : ρ₂ ≾ ρ₂')
           → []-≤ {[ ρ₂ ]ᵒ A} p ∘ᵐ [ ρ₁' ]ᶠ ([]-≤ {A} q) ∘ᵐ δ {A} {ρ₁'} {ρ₂'}
           ≈ᵐ δ {A} {ρ₁} {ρ₂} ∘ᵐ []-≤ {A} (·-mono-≾ p q)

    -- Graded comonad laws

    []-ε∘δ≡id : ∀ {A ρ}
              → ε {[ ρ ]ᵒ A} ∘ᵐ δ {A} {u} {ρ}
              ≈ᵐ []-≤ {A = A} (≃⇒≿ (·-identityˡ ρ))
    []-Dε∘δ≡id : ∀ {A ρ}
               → [ ρ ]ᶠ (ε {A}) ∘ᵐ δ {A} {ρ} {u}
               ≈ᵐ []-≤ {A} (≃⇒≿ (·-identityʳ ρ))
    []-δ∘δ≡Dδ∘δ : ∀ {A ρ₁ ρ₂ ρ₃}
                → δ {[ ρ₃ ]ᵒ A} {ρ₁} {ρ₂} ∘ᵐ δ {A} {ρ₁ · ρ₂} {ρ₃}
                ≈ᵐ    [ ρ₁ ]ᶠ (δ {A} {ρ₂} {ρ₃}) ∘ᵐ δ {A} {ρ₁} {ρ₂ · ρ₃}
                  ∘ᵐ []-≤ {A} (≃⇒≿ (·-assoc ρ₁ ρ₂ ρ₃))

    -- ηᵘ is natural

    ηᵘ-nat : ∀ {A B} → (f : A →ᵐ B) → [ u ]ᶠ f ∘ᵐ ηᵘ ≈ᵐ ηᵘ ∘ᵐ f

    -- ηᵘ and the counit ε are mutually inverse (so `[ u ]ᵒ A ≅ A`)

    []-ε∘ηᵘ≡id : ∀ {A} → ε {A} ∘ᵐ ηᵘ {A} ≈ᵐ idᵐ
    []-ηᵘ∘ε≡id : ∀ {A} → ηᵘ {A} ∘ᵐ ε {A} ≈ᵐ idᵐ

    -- []-monoidal is compatible with the projections, and is a section of the
    -- canonical projection pairing. Together these say the box preserves finite
    -- products: `[ ρ ]ᵒ (A ×ᵐ B) ≅ [ ρ ]ᵒ A ×ᵐ [ ρ ]ᵒ B`. They let a map into a
    -- boxed product be reconstructed from its two boxed projections.

    []-monoidal-fstᵐ : ∀ {A B ρ}
                     → [ ρ ]ᶠ (fstᵐ {A} {B}) ∘ᵐ []-monoidal ≈ᵐ fstᵐ
    []-monoidal-sndᵐ : ∀ {A B ρ}
                     → [ ρ ]ᶠ (sndᵐ {A} {B}) ∘ᵐ []-monoidal ≈ᵐ sndᵐ
    []-monoidal-η : ∀ {A B ρ}
                  → []-monoidal {A} {B} {ρ} ∘ᵐ ⟨ [ ρ ]ᶠ fstᵐ , [ ρ ]ᶠ sndᵐ ⟩ᵐ ≈ᵐ idᵐ

    -- The box preserves the terminal object: any two maps into `[ ρ ]ᵒ 𝟙ᵐ`
    -- agree (`[ ρ ]ᵒ 𝟙ᵐ ≅ 𝟙ᵐ`, the box being a right adjoint).

    []-𝟙-unique : ∀ {A ρ} → (f g : A →ᵐ [ ρ ]ᵒ 𝟙ᵐ) → f ≈ᵐ g
