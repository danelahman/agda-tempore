------------------------------------------------------------------------
-- The graded adjunction between the context modality `⟨ ρ ⟩` and the   --
-- box modality `[ ρ ]`, at a common resource grade `ρ`.                --
--                                                                    --
-- Semantically `⟨ ρ ⟩ ⊣ [ ρ ]`: the context modality (Kripke           --
-- possibility, `Σ` over accessible *past* worlds) is left adjoint to    --
-- the box modality (Kripke necessity, `∀` over accessible *future*      --
-- worlds). This adjunction is what interprets the Fitch-style formers:   --
-- the unit `η⊣` transposes a value typed under a lock into a boxed       --
-- value (the semantics of `box`), and the counit `ε⊣` extracts a boxed   --
-- value reached through a lock (the semantics of `unbox`).               --
--                                                                    --
-- The adjunction is *ungraded across the two sides* — both modalities    --
-- carry the same grade `ρ` — so the triangle identities need no grade    --
-- coercions.                                                           --
------------------------------------------------------------------------

open import Syntax.Grades

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past

module DenotationalSemantics.Model.Modality.Adjunction
         (Cat : Category)
         (G : Grade)
         (Fut : Future Cat G)
         (Pst : Past Cat G)
       where

open import Util.Equality

open Category Cat
open Grade G
open Future Fut
open Past Pst

record Adjunction : Set₁ where

  field

    -- STRUCTURE

    -- Unit: transpose a value under a lock into a boxed value.

    η⊣ : ∀ {A ρ} → A →ᵐ [ ρ ]ᵒ (⟨ ρ ⟩ᵒ A)

    -- Counit: extract a boxed value reached through a lock.

    ε⊣ : ∀ {A ρ} → ⟨ ρ ⟩ᵒ ([ ρ ]ᵒ A) →ᵐ A

    -- PROPERTIES

    -- unit and counit are natural

    η⊣-nat : ∀ {A B ρ} → (f : A →ᵐ B)
           → [ ρ ]ᶠ (⟨ ρ ⟩ᶠ f) ∘ᵐ η⊣ ≈ᵐ η⊣ ∘ᵐ f

    ε⊣-nat : ∀ {A B ρ} → (f : A →ᵐ B)
           → f ∘ᵐ ε⊣ ≈ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ ([ ρ ]ᶠ f)

    -- unit and counit are compatible with the grading: transposing
    -- along `η⊣` / `ε⊣` commutes with relaxing the grade. Because the
    -- box is contravariant and the context modality covariant in the
    -- grade, relaxing `ρ₁ ≾ ρ₂` on one side is matched by the functorial
    -- action of the other modality on the same relaxation.

    η⊣-≤ : ∀ {A ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
         → []-≤ p ∘ᵐ η⊣ {A} {ρ₂} ≈ᵐ [ ρ₁ ]ᶠ (⟨⟩-≤ p) ∘ᵐ η⊣ {A} {ρ₁}

    ε⊣-≤ : ∀ {A ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
         → ε⊣ {A} {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ ε⊣ {A} {ρ₁} ∘ᵐ ⟨ ρ₁ ⟩ᶠ ([]-≤ p)

    -- triangle identities

    triangleˡ : ∀ {A ρ}
              → ε⊣ {⟨ ρ ⟩ᵒ A} {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (η⊣ {A} {ρ}) ≈ᵐ idᵐ

    triangleʳ : ∀ {A ρ}
              → [ ρ ]ᶠ (ε⊣ {A} {ρ}) ∘ᵐ η⊣ {[ ρ ]ᵒ A} {ρ} ≈ᵐ idᵐ

    -- At the *unit* grade the adjunction restricts to the unit-graded
    -- isomorphisms `⟨ u ⟩ᵒ A ≅ A` and `[ u ]ᵒ A ≅ A`: the counit `ε⊣`
    -- factors through the box counit `ε` and the possibility counit `εᵘ`,
    -- and dually (by symmetry) the unit `η⊣` factors through the box unit
    -- `ηᵘ` and the possibility unit `η`. This is what makes a variable of
    -- *eternal* type usable at the unit grade: `extᵉ { u } ∘ η ≈ idᵐ`.

    ε⊣-u : ∀ {A} → ε⊣ {A} {u} ≈ᵐ εᵘ ∘ᵐ ⟨ u ⟩ᶠ ε
    η⊣-u : ∀ {A} → η⊣ {A} {u} ≈ᵐ [ u ]ᶠ η ∘ᵐ ηᵘ

    -- The graded adjunction is compatible with *composition* of grades:
    -- transposing at a product grade `ρ₁ · ρ₂` and then splitting the box
    -- with the comultiplication `δ` is the same as transposing twice, once
    -- at each factor, and folding the two resulting pasts with `μ`.
    --
    -- This is the mate law tying `Future.δ` to `Past.μ`; it is what lets a
    -- boxed environment be carried across a computation that is itself split
    -- into two graded phases (the `strᵀ-μᵀ` shape).

    η⊣-δ : ∀ {A ρ₁ ρ₂}
         → δ ∘ᵐ η⊣ {A} {ρ₁ · ρ₂}
         ≈ᵐ [ ρ₁ ]ᶠ ([ ρ₂ ]ᶠ (μ {A} {ρ₂} {ρ₁}) ∘ᵐ η⊣ {⟨ ρ₁ ⟩ᵒ A} {ρ₂})
             ∘ᵐ η⊣ {A} {ρ₁}

    -- The unit is compatible with the box's monoidal structure: transposing a
    -- value twice and pairing the two boxes gives the same as transposing the
    -- pair. (Both name the *same* future, so the two boxes agree witness by
    -- witness — that is what makes the lax monoidality enough here.)
    --
    -- This is what lets an environment box cross a `delay`: `delayᵀ`'s
    -- strength law routes the box through `[]-monoidal`.

    η⊣-monoidal : ∀ {A ρ}
                → []-monoidal ∘ᵐ ⟨ η⊣ {A} {ρ} , η⊣ {A} {ρ} ⟩ᵐ
                ≈ᵐ [ ρ ]ᶠ ⟨ idᵐ , idᵐ ⟩ᵐ ∘ᵐ η⊣ {A} {ρ}
