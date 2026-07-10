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

    -- triangle identities

    triangleˡ : ∀ {A ρ}
              → ε⊣ {⟨ ρ ⟩ᵒ A} {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (η⊣ {A} {ρ}) ≈ᵐ idᵐ

    triangleʳ : ∀ {A ρ}
              → [ ρ ]ᶠ (ε⊣ {A} {ρ}) ∘ᵐ η⊣ {[ ρ ]ᵒ A} {ρ} ≈ᵐ idᵐ
