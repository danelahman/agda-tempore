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
-- We additionally carry the *other direction* as a STRENGTH condition:  --
--                                                                    --
--   * `strᵉ : ⟨ ρ ⟩ᵒ X ×ᵐ A →ᵐ ⟨ ρ ⟩ᵒ (X ×ᵐ A)`  — the `⟨_⟩`-strength   --
--     at every grade. The functor `⟨ ρ ⟩` is *not* strong in general    --
--     (a possibility/diamond cannot drag an arbitrary object into the    --
--     past); it becomes strong exactly against an *eternal* object,      --
--     whose value is available at the past world the `⟨ ρ ⟩X` bundle     --
--     already witnesses. Dually `necᵉ` supplies the `[_]`-strength       --
--     `[ ρ ]ᵒ X ×ᵐ A →ᵐ [ ρ ]ᵒ (X ×ᵐ A)` (via `necᵉ` + `[]-monoidal`).   --
--                                                                    --
-- `strᵉ` is inverse to the canonical costrength                          --
-- `⟨ ⟨ ρ ⟩ᶠ fstᵐ , extᵉ ∘ ⟨ ρ ⟩ᶠ sndᵐ ⟩` (which always exists, from      --
-- `extᵉ`), so together they exhibit the distributivity isomorphism       --
--                                                                    --
--   `⟨ ρ ⟩ᵒ (X ×ᵐ A) ≅ ⟨ ρ ⟩ᵒ X ×ᵐ A`.                                  --
--                                                                    --
-- Note (why the distributivity iso, not `A ≅ [ ρ ]ᵒ A`): the naive       --
-- `A ≅ [ ρ ]ᵒ A` is too strong — it fails for `Empty` in non-serial      --
-- frames (`[ ρ ]ᵒ 𝟘 ≅ 𝟙` when a world has no `ρ`-future), and dually     --
-- `⟨ ρ ⟩ᵒ A ≅ A` fails for `Unit` (`⟨ ρ ⟩ᵒ 𝟙` counts accessible pasts).  --
-- The *distributivity* iso survives both (at `A = Unit` both sides are   --
-- `⟨ ρ ⟩ᵒ X`; at `A = Empty` both are `𝟘`), and holds for all eternal    --
-- formers with no seriality assumption. The `necᵉ`/`extᵉ` coalgebra/     --
-- algebra pair is precisely the `[_]`-half of the same picture.          --
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

record Eternalᵒ (A : Obj) : Set₁ where

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

    -- STRENGTH (the other direction)

    -- The `⟨_⟩`-strength at every grade: an eternal object is pulled
    -- *inside* the (past) context modality. `⟨ ρ ⟩` is not strong in
    -- general — a diamond cannot drag an arbitrary object into the past —
    -- but it is strong against an eternal `A`, whose value is available at
    -- the past world the `⟨ ρ ⟩X` bundle already witnesses. This is the
    -- companion of `necᵉ`, which supplies the dual `[_]`-strength.

    strᵉ : ∀ {ρ X} → ⟨ ρ ⟩ᵒ X ×ᵐ A →ᵐ ⟨ ρ ⟩ᵒ (X ×ᵐ A)

  -- The canonical costrength: the inverse direction of the distributivity iso,
  -- always available from `extᵉ` (project the `⟨ ρ ⟩X` factor, extract the
  -- eternal one). Defined here so the iso laws below can relate `strᵉ` to it.

  costrᵉ : ∀ {ρ X} → ⟨ ρ ⟩ᵒ (X ×ᵐ A) →ᵐ ⟨ ρ ⟩ᵒ X ×ᵐ A
  costrᵉ {ρ} = ⟨ ⟨ ρ ⟩ᶠ fstᵐ , extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ

  field

    -- `strᵉ` is a two-sided inverse of `costrᵉ`: together they exhibit the
    -- distributivity isomorphism `⟨ ρ ⟩ᵒ (X ×ᵐ A) ≅ ⟨ ρ ⟩ᵒ X ×ᵐ A`.
    --
    -- No naturality (in `X`) or grade-coherence (with `⟨⟩-≤`/`μ`/`η`) law is
    -- carried, because both are *derivable*, not primitive: `costrᵉ` is a
    -- composite of natural, grade-coherent pieces (`⟨ ρ ⟩ᶠ`, `fstᵐ`, `sndᵐ`,
    -- `extᵉ`), so it is natural/coherent; and `strᵉ`, being its two-sided
    -- inverse, inherits naturality/coherence (the inverse of a natural iso is
    -- natural). Keeping them derived avoids extra per-instance obligations.

    strᵉ-costrᵉ : ∀ {ρ X} → costrᵉ {ρ} {X} ∘ᵐ strᵉ {ρ} {X} ≈ᵐ idᵐ

    costrᵉ-strᵉ : ∀ {ρ X} → strᵉ {ρ} {X} ∘ᵐ costrᵉ {ρ} {X} ≈ᵐ idᵐ

  -- The strength's β-rules: reading back the two factors after `strᵉ` recovers
  -- them. Immediate from `strᵉ-costrᵉ` (`costrᵉ ∘ strᵉ ≈ id`) and the product
  -- projections of `costrᵉ`. They isolate `strᵉ`'s two components for reuse.

  strᵉ-fstᵐ : ∀ {ρ X} → ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ strᵉ {ρ} {X} ≈ᵐ fstᵐ
  strᵉ-fstᵐ = ≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _)))
              (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (≈ᵐ-trans (∘ᵐ-congʳ strᵉ-costrᵉ) (∘ᵐ-identityʳ _)))

  strᵉ-sndᵐ : ∀ {ρ X} → extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ strᵉ {ρ} {X} ≈ᵐ sndᵐ
  strᵉ-sndᵐ = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _)))
              (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
              (≈ᵐ-trans (∘ᵐ-congʳ strᵉ-costrᵉ) (∘ᵐ-identityʳ _))))

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
