------------------------------------------------------------------------
-- Uniform graded `[_]`-coalgebras.                                    --
--                                                                    --
-- The box-part of the `Eternalᵒ` structure: an object `A` with a      --
-- necessitation `necᵉ : A →ᵐ [ ρ ]ᵒ A` at every grade `ρ`, uniform in --
-- `ρ` (a graded `[_]`-coalgebra). This is exactly what lets such an   --
-- object be carried *under* a box — across the passage of time — and  --
-- so serve as the eternal parameter threaded through effect handling. --
--                                                                    --
-- It is stated purely over `Future` (no `Past`/adjunction), so it is  --
-- available in the monad's scope; `Eternalᵒ` yields one by dropping   --
-- its extraction half (`eternalᵒ-boxCoalg`).                          --
------------------------------------------------------------------------

open import Syntax.Grades

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future

module DenotationalSemantics.Model.Modality.BoxCoalg
         (Cat : Category)
         (G : Grade)
         (Fut : Future Cat G)
       where

open import Util.Equality

open Category Cat
open Grade G
open Future Fut

record BoxCoalg (A : Obj) : Set where

  field

    -- Necessitation at every grade.

    necᵉ : ∀ {ρ} → A →ᵐ [ ρ ]ᵒ A

    -- At the unit grade it is the box's unit `ηᵘ`.

    necᵉ-u : necᵉ {u} ≈ᵐ ηᵘ

    -- It is uniform in the grade (compatible with `[]-≤`).

    necᵉ-≤ : ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
           → []-≤ p ∘ᵐ necᵉ {ρ₂} ≈ᵐ necᵉ {ρ₁}

    -- It is compatible with the comultiplication `δ`.

    necᵉ-δ : ∀ {ρ₁ ρ₂}
           → δ ∘ᵐ necᵉ {ρ₁ · ρ₂} ≈ᵐ [ ρ₁ ]ᶠ (necᵉ {ρ₂}) ∘ᵐ necᵉ {ρ₁}
