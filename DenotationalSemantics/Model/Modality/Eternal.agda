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

-- PRODUCT CLOSURE OF THE ⟨_⟩-STRENGTH
--
-- Given two eternal objects, the `⟨_⟩`-strength for their product is assembled
-- from the factors' strengths, reassociating around them. It is inverse to the
-- reverse composite of the factors' costrengths (`costr-×`). These are the
-- ingredients a model's product-closure supplies for the `strᵉ`/`strᵉ-costrᵉ`/
-- `costrᵉ-strᵉ` fields; proved here abstractly (so the model reuses them rather
-- than re-deriving in a setting where `_≈ᵐ_` computes on the codomain object).

module ×-strength {A B : Obj} (eA : Eternalᵒ A) (eB : Eternalᵒ B) where

  private
    module EA = Eternalᵒ eA
    module EB = Eternalᵒ eB

  -- the product strength: bring `A` inside via `eA`, then `B` via `eB`
  strᵉ-× : ∀ {ρ X} → ⟨ ρ ⟩ᵒ X ×ᵐ (A ×ᵐ B) →ᵐ ⟨ ρ ⟩ᵒ (X ×ᵐ (A ×ᵐ B))
  strᵉ-× {ρ} = ⟨ ρ ⟩ᶠ ×ᵐ-assoc ∘ᵐ EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹

  -- its inverse: the reverse composite of the factor costrengths
  costr-× : ∀ {ρ X} → ⟨ ρ ⟩ᵒ (X ×ᵐ (A ×ᵐ B)) →ᵐ ⟨ ρ ⟩ᵒ X ×ᵐ (A ×ᵐ B)
  costr-× {ρ} = ×ᵐ-assoc ∘ᵐ mapˣᵐ EA.costrᵉ idᵐ ∘ᵐ EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹

  -- `mapˣᵐ EA.strᵉ id` and `mapˣᵐ EA.costrᵉ id` cancel (from `EA.costrᵉ-strᵉ`)
  private
    n∘h : ∀ {ρ X} → mapˣᵐ (EA.strᵉ {ρ} {X}) (idᵐ {B}) ∘ᵐ mapˣᵐ (EA.costrᵉ {ρ} {X}) (idᵐ {B}) ≈ᵐ idᵐ
    n∘h = ≈ᵐ-trans (mapˣᵐ-∘ EA.strᵉ idᵐ EA.costrᵉ idᵐ)
          (≈ᵐ-trans (mapˣᵐ-cong EA.costrᵉ-strᵉ (∘ᵐ-identityˡ idᵐ)) mapˣᵐ-idᵐ)

  -- `strᵉ-×` inverts `costr-×`: telescope the factor iso laws.
  strᵉ-×-costr-× : ∀ {ρ X} → strᵉ-× {ρ} {X} ∘ᵐ costr-× {ρ} {X} ≈ᵐ idᵐ
  strᵉ-×-costr-× {ρ} {X} =
    ≈ᵐ-trans (∘ᵐ-assoc (⟨ ρ ⟩ᶠ ×ᵐ-assoc)
                (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹) (costr-× {ρ} {X}))
    (≈ᵐ-trans (∘ᵐ-congʳ REST)
    (≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ ×ᵐ-assoc ×ᵐ-assoc⁻¹))
    (≈ᵐ-trans (⟨⟩-congᶠ ×ᵐ-assoc-iso) ⟨⟩-idᵐ)))
    where
      P∘C : ×ᵐ-assoc⁻¹ ∘ᵐ costr-× {ρ} {X}
          ≈ᵐ mapˣᵐ EA.costrᵉ idᵐ ∘ᵐ EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹
      P∘C = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc ×ᵐ-assoc⁻¹ ×ᵐ-assoc _))
            (≈ᵐ-trans (∘ᵐ-congˡ ×ᵐ-assoc⁻¹-iso) (∘ᵐ-identityˡ _))
      INNER : (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ costr-× {ρ} {X}
            ≈ᵐ EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹
      INNER = ≈ᵐ-trans (∘ᵐ-assoc (mapˣᵐ EA.strᵉ idᵐ) ×ᵐ-assoc⁻¹ (costr-× {ρ} {X}))
              (≈ᵐ-trans (∘ᵐ-congʳ P∘C)
              (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (mapˣᵐ EA.strᵉ idᵐ) (mapˣᵐ EA.costrᵉ idᵐ) _))
              (≈ᵐ-trans (∘ᵐ-congˡ n∘h) (∘ᵐ-identityˡ _))))
      REST : (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ costr-× {ρ} {X}
           ≈ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹
      REST = ≈ᵐ-trans (∘ᵐ-assoc EB.strᵉ (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹) (costr-× {ρ} {X}))
             (≈ᵐ-trans (∘ᵐ-congʳ INNER)
             (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc EB.strᵉ EB.costrᵉ _))
             (≈ᵐ-trans (∘ᵐ-congˡ EB.costrᵉ-strᵉ) (∘ᵐ-identityˡ _))))

  -- `costr-×` inverts `strᵉ-×`: the mirror telescope.
  costr-×-strᵉ-× : ∀ {ρ X} → costr-× {ρ} {X} ∘ᵐ strᵉ-× {ρ} {X} ≈ᵐ idᵐ
  costr-×-strᵉ-× {ρ} {X} =
    ≈ᵐ-trans (∘ᵐ-assoc ×ᵐ-assoc
                (mapˣᵐ EA.costrᵉ idᵐ ∘ᵐ EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹) (strᵉ-× {ρ} {X}))
    (≈ᵐ-trans (∘ᵐ-congʳ REST') ×ᵐ-assoc-iso)
    where
      aa : ⟨ ρ ⟩ᶠ (×ᵐ-assoc⁻¹ {X} {A} {B}) ∘ᵐ ⟨ ρ ⟩ᶠ (×ᵐ-assoc {X} {A} {B}) ≈ᵐ idᵐ
      aa = ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ ×ᵐ-assoc⁻¹ ×ᵐ-assoc))
           (≈ᵐ-trans (⟨⟩-congᶠ ×ᵐ-assoc⁻¹-iso) ⟨⟩-idᵐ)
      Q : ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹ ∘ᵐ strᵉ-× {ρ} {X}
        ≈ᵐ EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹
      Q = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹) (⟨ ρ ⟩ᶠ ×ᵐ-assoc)
                             (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
          (≈ᵐ-trans (∘ᵐ-congˡ aa) (∘ᵐ-identityˡ _))
      n∘h' : mapˣᵐ (EA.costrᵉ {ρ} {X}) (idᵐ {B}) ∘ᵐ mapˣᵐ (EA.strᵉ {ρ} {X}) (idᵐ {B}) ≈ᵐ idᵐ
      n∘h' = ≈ᵐ-trans (mapˣᵐ-∘ EA.costrᵉ idᵐ EA.strᵉ idᵐ)
             (≈ᵐ-trans (mapˣᵐ-cong EA.strᵉ-costrᵉ (∘ᵐ-identityˡ idᵐ)) mapˣᵐ-idᵐ)
      INNER' : (EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹) ∘ᵐ strᵉ-× {ρ} {X}
             ≈ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹
      INNER' = ≈ᵐ-trans (∘ᵐ-assoc EB.costrᵉ (⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹) (strᵉ-× {ρ} {X}))
               (≈ᵐ-trans (∘ᵐ-congʳ Q)
               (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc EB.costrᵉ EB.strᵉ _))
               (≈ᵐ-trans (∘ᵐ-congˡ EB.strᵉ-costrᵉ) (∘ᵐ-identityˡ _))))
      REST' : (mapˣᵐ EA.costrᵉ idᵐ ∘ᵐ EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹) ∘ᵐ strᵉ-× {ρ} {X}
            ≈ᵐ ×ᵐ-assoc⁻¹
      REST' = ≈ᵐ-trans (∘ᵐ-assoc (mapˣᵐ EA.costrᵉ idᵐ) (EB.costrᵉ ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc⁻¹) (strᵉ-× {ρ} {X}))
              (≈ᵐ-trans (∘ᵐ-congʳ INNER')
              (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (mapˣᵐ EA.costrᵉ idᵐ) (mapˣᵐ EA.strᵉ idᵐ) _))
              (≈ᵐ-trans (∘ᵐ-congˡ n∘h') (∘ᵐ-identityˡ _))))

  -- `⟨ρ⟩ᶠ fstᵐ` reads back through `strᵉ-×` to the first projection: the two
  -- factor strengths' `strᵉ-fstᵐ` laws threaded through the reassociations.
  strᵉ-×-fstᵐ : ∀ {ρ X} → ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ strᵉ-× {ρ} {X} ≈ᵐ fstᵐ
  strᵉ-×-fstᵐ {ρ} {X} =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ fstᵐ) (⟨ ρ ⟩ᶠ ×ᵐ-assoc)
                        (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ fstᵐ ×ᵐ-assoc)) (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _))))
    (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ fstᵐ fstᵐ))
    (≈ᵐ-trans (∘ᵐ-assoc (⟨ ρ ⟩ᶠ fstᵐ) (⟨ ρ ⟩ᶠ fstᵐ)
                 (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹))
    (≈ᵐ-trans (∘ᵐ-congʳ RB)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ fstᵐ) EA.strᵉ (fstᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
    (≈ᵐ-trans (∘ᵐ-congˡ EA.strᵉ-fstᵐ)
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _))))))))
    where
      -- `⟨ρ⟩ᶠfstᵐ ∘ (EB.strᵉ ∘ mapˣᵐ EA.strᵉ id ∘ ×ᵐ-assoc⁻¹) ≈ EA.strᵉ ∘ (fstᵐ ∘ ×ᵐ-assoc⁻¹)`
      RB : ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)
         ≈ᵐ EA.strᵉ ∘ᵐ (fstᵐ ∘ᵐ ×ᵐ-assoc⁻¹)
      RB = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ fstᵐ) EB.strᵉ (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
           (≈ᵐ-trans (∘ᵐ-congˡ EB.strᵉ-fstᵐ)
           (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ (mapˣᵐ EA.strᵉ idᵐ) ×ᵐ-assoc⁻¹))
           (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                     (∘ᵐ-assoc EA.strᵉ fstᵐ ×ᵐ-assoc⁻¹))))

  -- The A-projection reads back through `strᵉ-×` (with `EA.extᵉ`) to `fstᵐ∘sndᵐ`:
  -- `⟨ρ⟩ᶠ(fstᵐ∘sndᵐ)` picks the `A` factor, `EA.strᵉ-sndᵐ` extracts it.
  strᵉ-×-snd-fst : ∀ {ρ X}
    → EA.extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ (fstᵐ ∘ᵐ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X} ≈ᵐ fstᵐ ∘ᵐ sndᵐ
  strᵉ-×-snd-fst {ρ} {X} =
    ≈ᵐ-trans (∘ᵐ-congʳ SUB)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc EA.extᵉ (⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ EA.strᵉ) (fstᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
    (≈ᵐ-trans (∘ᵐ-congˡ EA.strᵉ-sndᵐ)
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _))))
    where
      -- `⟨ρ⟩ᶠ(fstᵐ∘sndᵐ) ∘ strᵉ-× ≈ (⟨ρ⟩ᶠsndᵐ ∘ EA.strᵉ) ∘ (fstᵐ ∘ ×ᵐ-assoc⁻¹)`
      SUB : ⟨ ρ ⟩ᶠ (fstᵐ ∘ᵐ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X}
          ≈ᵐ (⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ EA.strᵉ) ∘ᵐ (fstᵐ ∘ᵐ ×ᵐ-assoc⁻¹)
      SUB = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ (fstᵐ ∘ᵐ sndᵐ)) (⟨ ρ ⟩ᶠ ×ᵐ-assoc)
                               (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
            (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ (fstᵐ ∘ᵐ sndᵐ) ×ᵐ-assoc))
                        (⟨⟩-congᶠ (≈ᵐ-trans (∘ᵐ-assoc fstᵐ sndᵐ ×ᵐ-assoc)
                                  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _))))))
            (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-∘ᵐ sndᵐ fstᵐ))
            (≈ᵐ-trans (∘ᵐ-assoc (⟨ ρ ⟩ᶠ sndᵐ) (⟨ ρ ⟩ᶠ fstᵐ)
                         (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹))
            (≈ᵐ-trans (∘ᵐ-congʳ RB2)
                      (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ sndᵐ) EA.strᵉ (fstᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))))))
        where
          RB2 : ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)
              ≈ᵐ EA.strᵉ ∘ᵐ (fstᵐ ∘ᵐ ×ᵐ-assoc⁻¹)
          RB2 = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ fstᵐ) EB.strᵉ (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
                (≈ᵐ-trans (∘ᵐ-congˡ EB.strᵉ-fstᵐ)
                (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ (mapˣᵐ EA.strᵉ idᵐ) ×ᵐ-assoc⁻¹))
                (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
                          (∘ᵐ-assoc EA.strᵉ fstᵐ ×ᵐ-assoc⁻¹))))

  -- The B-projection reads back through `strᵉ-×` (with `EB.extᵉ`) to `sndᵐ∘sndᵐ`.
  strᵉ-×-snd-snd : ∀ {ρ X}
    → EB.extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X} ≈ᵐ sndᵐ ∘ᵐ sndᵐ
  strᵉ-×-snd-snd {ρ} {X} =
    ≈ᵐ-trans (∘ᵐ-congʳ SUB2)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc EB.extᵉ (⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ EB.strᵉ)
                        (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
    (≈ᵐ-trans (∘ᵐ-congˡ EB.strᵉ-sndᵐ)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ (mapˣᵐ EA.strᵉ idᵐ) ×ᵐ-assoc⁻¹))
    (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityˡ sndᵐ)) (⟨⟩ᵐ-sndᵐ _ _))))))
    where
      SUB2 : ⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X}
           ≈ᵐ (⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ EB.strᵉ) ∘ᵐ (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)
      SUB2 = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ sndᵐ)) (⟨ ρ ⟩ᶠ ×ᵐ-assoc)
                               (EB.strᵉ ∘ᵐ mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹)))
             (≈ᵐ-trans (∘ᵐ-congˡ SS)
                       (≈ᵐ-sym (∘ᵐ-assoc (⟨ ρ ⟩ᶠ sndᵐ) EB.strᵉ (mapˣᵐ EA.strᵉ idᵐ ∘ᵐ ×ᵐ-assoc⁻¹))))
        where
          SS : ⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ sndᵐ) ∘ᵐ ⟨ ρ ⟩ᶠ ×ᵐ-assoc ≈ᵐ ⟨ ρ ⟩ᶠ sndᵐ
          SS = ≈ᵐ-trans (≈ᵐ-sym (⟨⟩-∘ᵐ (sndᵐ ∘ᵐ sndᵐ) ×ᵐ-assoc))
               (⟨⟩-congᶠ (≈ᵐ-trans (∘ᵐ-assoc sndᵐ sndᵐ ×ᵐ-assoc)
                         (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _))))

  -- Given the product's extraction `ext×` and its decomposition into the
  -- factors' extractions, the canonical costrength of the product coincides
  -- with `costr-×`, so `strᵉ-×` is its two-sided inverse — the two `Eternalᵒ`
  -- law fields a product-closure needs (`strᵉ = strᵉ-×`, `extᵉ = ext×`).
  module product-laws
           (ext× : ∀ {ρ} → ⟨ ρ ⟩ᵒ (A ×ᵐ B) →ᵐ A ×ᵐ B)
           (ext×-dec : ∀ {ρ} → ext× {ρ}
                     ≈ᵐ ⟨ EA.extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ , EB.extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ) where

    -- the canonical costrength w.r.t. `ext×` (the record's derived `costrᵉ`)
    canon-× : ∀ {ρ X} → ⟨ ρ ⟩ᵒ (X ×ᵐ (A ×ᵐ B)) →ᵐ ⟨ ρ ⟩ᵒ X ×ᵐ (A ×ᵐ B)
    canon-× {ρ} = ⟨ ⟨ ρ ⟩ᶠ fstᵐ , ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ

    fst-ext× : ∀ {ρ} → fstᵐ ∘ᵐ ext× {ρ} ≈ᵐ EA.extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
    fst-ext× = ≈ᵐ-trans (∘ᵐ-congʳ ext×-dec) (⟨⟩ᵐ-fstᵐ _ _)

    snd-ext× : ∀ {ρ} → sndᵐ ∘ᵐ ext× {ρ} ≈ᵐ EB.extᵉ ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ
    snd-ext× = ≈ᵐ-trans (∘ᵐ-congʳ ext×-dec) (⟨⟩ᵐ-sndᵐ _ _)

    -- `(ext× ∘ ⟨ρ⟩ᶠsndᵐ) ∘ strᵉ-× ≈ sndᵐ`, by prod-ext into the two factors
    strᵉ-×-sndᵐ : ∀ {ρ X} → (ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X} ≈ᵐ sndᵐ
    strᵉ-×-sndᵐ {ρ} {X} =
      ≈ᵐ-trans (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ sndᵐ) (sndᵐ ∘ᵐ sndᵐ)
                  ((ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X}) Acomp Bcomp)
      (≈ᵐ-sym (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ sndᵐ) (sndᵐ ∘ᵐ sndᵐ) sndᵐ ≈ᵐ-refl ≈ᵐ-refl))
      where
        Acomp : fstᵐ ∘ᵐ ((ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X}) ≈ᵐ fstᵐ ∘ᵐ sndᵐ
        Acomp =
          ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ (ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ) (strᵉ-× {ρ} {X})))
          (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc fstᵐ ext× (⟨ ρ ⟩ᶠ sndᵐ))))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ fst-ext×))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc EA.extᵉ (⟨ ρ ⟩ᶠ fstᵐ) (⟨ ρ ⟩ᶠ sndᵐ)))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ fstᵐ sndᵐ))))
          (≈ᵐ-trans (∘ᵐ-assoc EA.extᵉ (⟨ ρ ⟩ᶠ (fstᵐ ∘ᵐ sndᵐ)) (strᵉ-× {ρ} {X}))
                    strᵉ-×-snd-fst)))))
        Bcomp : sndᵐ ∘ᵐ ((ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ) ∘ᵐ strᵉ-× {ρ} {X}) ≈ᵐ sndᵐ ∘ᵐ sndᵐ
        Bcomp =
          ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ (ext× ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ) (strᵉ-× {ρ} {X})))
          (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc sndᵐ ext× (⟨ ρ ⟩ᶠ sndᵐ))))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congˡ snd-ext×))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-assoc EB.extᵉ (⟨ ρ ⟩ᶠ sndᵐ) (⟨ ρ ⟩ᶠ sndᵐ)))
          (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ sndᵐ sndᵐ))))
          (≈ᵐ-trans (∘ᵐ-assoc EB.extᵉ (⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ sndᵐ)) (strᵉ-× {ρ} {X}))
                    strᵉ-×-snd-snd)))))

    -- The record's `strᵉ-costrᵉ`: `canon-× ∘ strᵉ-× ≈ id`.
    strᵉ-costrᵉ-× : ∀ {ρ X} → canon-× {ρ} {X} ∘ᵐ strᵉ-× {ρ} {X} ≈ᵐ idᵐ
    strᵉ-costrᵉ-× {ρ} {X} =
      ≈ᵐ-trans (⟨⟩ᵐ-unique fstᵐ sndᵐ (canon-× {ρ} {X} ∘ᵐ strᵉ-× {ρ} {X}) C1 C2)
      (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ fstᵐ) (∘ᵐ-identityʳ sndᵐ)))
      where
        C1 : fstᵐ ∘ᵐ (canon-× {ρ} {X} ∘ᵐ strᵉ-× {ρ} {X}) ≈ᵐ fstᵐ
        C1 = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ (canon-× {ρ} {X}) (strᵉ-× {ρ} {X})))
             (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)) strᵉ-×-fstᵐ)
        C2 : sndᵐ ∘ᵐ (canon-× {ρ} {X} ∘ᵐ strᵉ-× {ρ} {X}) ≈ᵐ sndᵐ
        C2 = ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ (canon-× {ρ} {X}) (strᵉ-× {ρ} {X})))
             (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)) strᵉ-×-sndᵐ)

    -- `canon-× ≈ costr-×` by inverse uniqueness, hence the second law.
    bridge : ∀ {ρ X} → canon-× {ρ} {X} ≈ᵐ costr-× {ρ} {X}
    bridge {ρ} {X} =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ (canon-× {ρ} {X})))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym strᵉ-×-costr-×))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc (canon-× {ρ} {X}) (strᵉ-× {ρ} {X}) (costr-× {ρ} {X})))
      (≈ᵐ-trans (∘ᵐ-congˡ strᵉ-costrᵉ-×) (∘ᵐ-identityˡ _))))

    costrᵉ-strᵉ-× : ∀ {ρ X} → strᵉ-× {ρ} {X} ∘ᵐ canon-× {ρ} {X} ≈ᵐ idᵐ
    costrᵉ-strᵉ-× = ≈ᵐ-trans (∘ᵐ-congʳ bridge) strᵉ-×-costr-×
