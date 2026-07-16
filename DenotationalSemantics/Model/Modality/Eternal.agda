------------------------------------------------------------------------
-- Objects interpreting *eternal* types.                                --
--                                                                    --
-- An eternal type (`Syntax.Types.Eternal`) is one whose values are    --
-- available regardless of the resource budget: the variable rule may   --
-- use a variable of eternal type at *any* grade `ρ`, not only at grades --
-- below the unit `u`. Semantically this is the grade-`u` isomorphism    --
-- `[ u ]ᵒ A ≅ A` (the box counit `ε` / unit `ηᵘ`) generalised to hold   --
-- at every grade — but only *one-directionally*, as a graded comonad    --
-- coalgebra, not as an isomorphism (see the note below).               --
--                                                                    --
-- Concretely (`Example.PSh`) eternal types are the constant             --
-- presheaves: their value is the same at every world, so it can be      --
-- necessitated into, and extracted from, the box / context modality at  --
-- an arbitrary grade.                                                   --
--                                                                    --
-- We carry *both* transposes of the structure, tied by the graded       --
-- adjunction `⟨ ρ ⟩ ⊣ [ ρ ]`:                                          --
--                                                                    --
--   * `necᵉ : A →ᵐ [ ρ ]ᵒ A`  — necessitation at every grade, the       --
--     graded `[_]`-coalgebra generalising `ηᵘ`;                         --
--   * `extᵉ : ⟨ ρ ⟩ᵒ A →ᵐ A`  — extraction at every grade, the graded   --
--     `⟨_⟩`-algebra generalising `εᵘ`, which is what the variable rule   --
--     consumes directly.                                                --
--                                                                    --
-- A single law `extᵉ-mate` states they are adjoint mates; the reverse   --
-- mate `necᵉ-mate` is then derivable from the triangle identities.      --
--                                                                    --
-- Note (why not an isomorphism): requiring `A ≅ [ ρ ]ᵒ A` would be too  --
-- strong. It fails for `Empty` in non-serial frames (`[ ρ ]ᵒ 𝟘 ≅ 𝟙`    --
-- when a world has no `ρ`-future) and, dually, `⟨ ρ ⟩ᵒ A ≅ A` fails for --
-- `Unit` (`⟨ ρ ⟩ᵒ 𝟙` counts accessible pasts). The one-directional      --
-- coalgebra/algebra pair holds for all eternal formers with no          --
-- seriality assumption, and is exactly what the calculus needs.         --
------------------------------------------------------------------------

open import Syntax.Grades

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction

module DenotationalSemantics.Model.Modality.Eternal
         (Cat : Category)
         (G : Grade)
         (Fut : Future Cat G)
         (Pst : Past Cat G)
         (Adj : Adjunction Cat G Fut Pst)
       where

open import Util.Equality

open import DenotationalSemantics.Model.Modality.BoxCoalg Cat G Fut

open Category Cat
open Grade G
open Future Fut
open Past Pst
open Adjunction Adj

record Eternalᵒ (A : Obj) : Set where

  field

    -- STRUCTURE

    -- Necessitation at every grade (generalises `ηᵘ` from `u` to all `ρ`).

    necᵉ : ∀ {ρ} → A →ᵐ [ ρ ]ᵒ A

    -- Extraction at every grade (generalises `εᵘ`); consumed by `var`.

    extᵉ : ∀ {ρ} → ⟨ ρ ⟩ᵒ A →ᵐ A

    -- PROPERTIES

    -- `necᵉ` and `extᵉ` are adjoint mates under `⟨ ρ ⟩ ⊣ [ ρ ]`.

    extᵉ-mate : ∀ {ρ} → extᵉ {ρ} ≈ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ (necᵉ {ρ})

    -- `necᵉ` is a uniform graded `[_]`-coalgebra:

    -- at the unit grade it is the box's unit `ηᵘ`,

    necᵉ-u : necᵉ {u} ≈ᵐ ηᵘ

    -- it is uniform in the grade (compatible with `[]-≤`),

    necᵉ-≤ : ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
           → []-≤ p ∘ᵐ necᵉ {ρ₂} ≈ᵐ necᵉ {ρ₁}

    -- and it is compatible with the comultiplication `δ`.

    necᵉ-δ : ∀ {ρ₁ ρ₂}
           → δ ∘ᵐ necᵉ {ρ₁ · ρ₂} ≈ᵐ [ ρ₁ ]ᶠ (necᵉ {ρ₂}) ∘ᵐ necᵉ {ρ₁}

    -- Dually, `extᵉ` is a graded `⟨_⟩`-algebra: extracting from a nested
    -- possibility agrees with folding the two layers with `μ` and
    -- extracting once. (The `⟨_⟩`-algebra multiplication law. It is not
    -- derivable from `extᵉ-mate` and `necᵉ-δ`, since the adjunction
    -- carries no law relating `Past.μ` with `Future.δ`.)

    extᵉ-μ : ∀ {ρ₁ ρ₂}
           → extᵉ {ρ₂ · ρ₁} ∘ᵐ μ {A} {ρ₁} {ρ₂}
           ≈ᵐ extᵉ {ρ₁} ∘ᵐ ⟨ ρ₁ ⟩ᶠ (extᵉ {ρ₂})

  -- The reverse mate, derivable from `extᵉ-mate` and the right triangle
  -- identity: `necᵉ` is recovered by transposing `extᵉ` back.

  necᵉ-mate : ∀ {ρ} → necᵉ {ρ} ≈ᵐ [ ρ ]ᶠ (extᵉ {ρ}) ∘ᵐ η⊣
  necᵉ-mate {ρ} = ≈ᵐ-sym (≈ᵐ-trans
    (∘ᵐ-congˡ ([]-congᶠ extᵉ-mate))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ (⟨ ρ ⟩ᶠ necᵉ) ε⊣))
    (≈ᵐ-trans (∘ᵐ-assoc ([ ρ ]ᶠ ε⊣) ([ ρ ]ᶠ (⟨ ρ ⟩ᶠ necᵉ)) η⊣)
    (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat necᵉ))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc ([ ρ ]ᶠ ε⊣) η⊣ necᵉ))
    (≈ᵐ-trans (∘ᵐ-congˡ triangleʳ)
              (∘ᵐ-identityˡ necᵉ)))))))

  -- Extraction is uniform in the grade: extracting at `ρ₂` after relaxing
  -- along `ρ₁ ≾ ρ₂` agrees with extracting directly at `ρ₁`. Derived from
  -- `extᵉ-mate`, the naturality of `⟨⟩-≤`/`ε⊣`, and `necᵉ`'s uniformity
  -- `necᵉ-≤`. This is what makes a variable of eternal type interpretable
  -- independently of how much its context has been relaxed.

  extᵉ-≤ : ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
         → extᵉ {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ extᵉ {ρ₁}
  extᵉ-≤ {ρ₁} {ρ₂} p =
    ≈ᵐ-trans (∘ᵐ-congˡ extᵉ-mate)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-nat (necᵉ {ρ₂}) p))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (ε⊣-≤ p))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ ([]-≤ p) (necᵉ {ρ₂}))))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ (necᵉ-≤ p)))
              (≈ᵐ-sym extᵉ-mate))))))))

  -- At the unit grade the eternal extraction is exactly the possibility
  -- counit `εᵘ`. This is where the adjunction's unit-grade restriction
  -- `ε⊣-u` is used, together with `necᵉ-u` and the box iso `ε ∘ ηᵘ ≈ id`.

  extᵉ-u : extᵉ {u} ≈ᵐ εᵘ
  extᵉ-u =
    ≈ᵐ-trans extᵉ-mate
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ necᵉ-u))
    (≈ᵐ-trans (∘ᵐ-congˡ ε⊣-u)
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ ε ηᵘ)))
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-congᶠ []-ε∘ηᵘ≡id))
    (≈ᵐ-trans (∘ᵐ-congʳ ⟨⟩-idᵐ)
              (∘ᵐ-identityʳ εᵘ)))))))

-- The box-part of an eternal structure: forgetting the extraction half
-- leaves a uniform graded `[_]`-coalgebra. This is what the effect handling
-- fold threads as its eternal parameter.

eternalᵒ-boxCoalg : ∀ {A} → Eternalᵒ A → BoxCoalg A
eternalᵒ-boxCoalg e = record
  { necᵉ   = Eternalᵒ.necᵉ e
  ; necᵉ-u = Eternalᵒ.necᵉ-u e
  ; necᵉ-≤ = Eternalᵒ.necᵉ-≤ e
  ; necᵉ-δ = Eternalᵒ.necᵉ-δ e
  }
