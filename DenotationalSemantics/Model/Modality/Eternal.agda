------------------------------------------------------------------------
-- Objects interpreting *eternal* types.                                --
--                                                                    --
-- An eternal type (`Syntax.Types.Eternal`) is one whose values are    --
-- available regardless of the resource budget: the variable rule may   --
-- use a variable of eternal type at *any* grade `ρ`, not only at grades --
-- below the unit `u`. Semantically this is the grade-`u` isomorphism    --
-- `[ u ]ᵒ A ≅ A` (the box counit `ε` / unit `ηᵘ`) generalised to hold   --
-- at every grade — but only *one-directionally*, as an algebra, not as  --
-- an isomorphism (see the note below).                                  --
--                                                                    --
-- Concretely (`Example.PSh`) eternal types are the constant             --
-- presheaves: their value is the same at every world, so it can be      --
-- necessitated into, and extracted from, the box / context modality at  --
-- an arbitrary grade.                                                   --
--                                                                    --
-- At the greatest grade `⊤` the context modality is an ordinary monad   --
-- (`⟨⊤⟩-η`/`⟨⊤⟩-μ` below), and an eternal object is exactly an          --
-- Eilenberg–Moore algebra for it:                                       --
--                                                                    --
--   * `α : ⟨ ⊤ ⟩ᵒ A →ᵐ A`, with a unit and an associativity law.        --
--                                                                    --
-- Extraction at an arbitrary grade is then `extᵉ {ρ} = α ∘ᵐ ⟨⟩-≤ (≾-⊤ ρ)` --
-- — the graded `⟨_⟩`-algebra generalising `εᵘ`, which is what the        --
-- variable rule consumes — and its three laws are derived: uniformity    --
-- in the grade from `≾`-irrelevance, the unit law from `α-unit`, the     --
-- multiplication law from `α-assoc`.                                     --
--                                                                    --
-- Its transpose under `⟨ ρ ⟩ ⊣ [ ρ ]`, necessitation                    --
-- `necᵉ : A →ᵐ [ ρ ]ᵒ A` — the graded `[_]`-coalgebra generalising      --
-- `ηᵘ` — is likewise derived, along with the mate laws `necᵉ-mate` /    --
-- `extᵉ-mate` and the coalgebra laws, so a model supplies only `α`.     --
--                                                                    --
-- Note (why an algebra, not `A ≅ [ ρ ]ᵒ A`): the naive `A ≅ [ ρ ]ᵒ A`   --
-- is too strong — it fails for `Empty` in non-serial frames             --
-- (`[ ρ ]ᵒ 𝟘 ≅ 𝟙` when a world has no `ρ`-future), and dually            --
-- `⟨ ρ ⟩ᵒ A ≅ A` fails for `Unit` (`⟨ ρ ⟩ᵒ 𝟙` counts accessible pasts).  --
-- The algebra/coalgebra pair survives both, with no seriality            --
-- assumption, and holds for all eternal formers.                         --
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

open Category Cat
open Grade G
open Future Fut
open Past Pst
open Adjunction Adj

-- THE `⟨ ⊤ ⟩` MONAD
--
-- At the greatest grade the graded context modality collapses to an ordinary
-- monad: `≾-⊤` relaxes the grades `u` and `⊤ · ⊤` produced by `η` and `μ` back
-- to `⊤`. Only `≾-⊤` is needed — `⊤` is not assumed absorbing.

⟨⊤⟩-η : ∀ {A} → A →ᵐ ⟨ ⊤ ⟩ᵒ A
⟨⊤⟩-η = ⟨⟩-≤ (≾-⊤ u) ∘ᵐ η

⟨⊤⟩-μ : ∀ {A} → ⟨ ⊤ ⟩ᵒ (⟨ ⊤ ⟩ᵒ A) →ᵐ ⟨ ⊤ ⟩ᵒ A
⟨⊤⟩-μ {A} = ⟨⟩-≤ (≾-⊤ (⊤ · ⊤)) ∘ᵐ μ {A} {⊤} {⊤}

-- The functorial action is that of `⟨ ⊤ ⟩ᶠ`; both natural transformations are
-- natural, being composites of natural ones.

⟨⊤⟩-η-nat : ∀ {A B} → (f : A →ᵐ B) → ⟨ ⊤ ⟩ᶠ f ∘ᵐ ⟨⊤⟩-η ≈ᵐ ⟨⊤⟩-η ∘ᵐ f
⟨⊤⟩-η-nat f =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-nat f (≾-⊤ u)))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-η-nat f))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

⟨⊤⟩-μ-nat : ∀ {A B} → (f : A →ᵐ B) → ⟨ ⊤ ⟩ᶠ f ∘ᵐ ⟨⊤⟩-μ ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨ ⊤ ⟩ᶠ f)
⟨⊤⟩-μ-nat f =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-nat f (≾-⊤ (⊤ · ⊤))))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-μ-nat f))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

-- LEFT UNIT, from `μ-εᵘ` and `⟨⟩-εᵘ∘η≡id`.

⟨⊤⟩-μ∘η≡id : ∀ {A} → ⟨⊤⟩-μ {A} ∘ᵐ ⟨⊤⟩-η {⟨ ⊤ ⟩ᵒ A} ≈ᵐ idᵐ
⟨⊤⟩-μ∘η≡id {A} =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ʳ (≾-⊤ u)))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (·-monoʳ-≾ (≾-⊤ u)) (≾-⊤ (⊤ · ⊤))))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-irr _ (≾-reflexive (·-identityʳ ⊤))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (μ-εᵘ {A} {⊤}))
            ⟨⟩-εᵘ∘η≡id))))))))

-- RIGHT UNIT, from `⟨⟩-μ∘Tη≡id`.

⟨⊤⟩-μ∘Tη≡id : ∀ {A} → ⟨⊤⟩-μ {A} ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨⊤⟩-η {A}) ≈ᵐ idᵐ
⟨⊤⟩-μ∘Tη≡id {A} =
  ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ (⟨⟩-≤ (≾-⊤ u)) η))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ (≾-⊤ u)))))
  (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (·-monoˡ-≾ (≾-⊤ u)) (≾-⊤ (⊤ · ⊤))))
  (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-μ∘Tη≡id {A} {⊤}))
  (≈ᵐ-trans (⟨⟩-≤-trans _ _)
  (≈ᵐ-trans (⟨⟩-≤-irr _ ≾-refl) ⟨⟩-≤-refl)))))))))

-- ASSOCIATIVITY, from `⟨⟩-μ∘μ≡μ∘Tμ`.

⟨⊤⟩-μ∘μ≡μ∘Tμ : ∀ {A} → ⟨⊤⟩-μ {A} ∘ᵐ ⟨⊤⟩-μ {⟨ ⊤ ⟩ᵒ A} ≈ᵐ ⟨⊤⟩-μ {A} ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨⊤⟩-μ {A})
⟨⊤⟩-μ∘μ≡μ∘Tμ {A} = ≈ᵐ-trans left (≈ᵐ-sym right)
  where
    mid : ⟨ ⊤ ⟩ᵒ (⟨ ⊤ ⟩ᵒ (⟨ ⊤ ⟩ᵒ A)) →ᵐ ⟨ ⊤ ⟩ᵒ A
    mid = ⟨⟩-≤ (≾-⊤ ((⊤ · ⊤) · ⊤))
            ∘ᵐ (μ {A} {⊤} {⊤ · ⊤} ∘ᵐ ⟨ ⊤ ⟩ᶠ (μ {A} {⊤} {⊤}))

    left : ⟨⊤⟩-μ {A} ∘ᵐ ⟨⊤⟩-μ {⟨ ⊤ ⟩ᵒ A} ≈ᵐ mid
    left =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ʳ (≾-⊤ (⊤ · ⊤))))))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (·-monoʳ-≾ (≾-⊤ (⊤ · ⊤))) (≾-⊤ (⊤ · ⊤))))
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-μ∘μ≡μ∘Tμ {A} {⊤} {⊤} {⊤}))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (≾-reflexive (·-assoc ⊤ ⊤ ⊤)) _))
                (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))))))))))

    right : ⟨⊤⟩-μ {A} ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨⊤⟩-μ {A}) ≈ᵐ mid
    right =
      ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ (⟨⟩-≤ (≾-⊤ (⊤ · ⊤))) (μ {A} {⊤} {⊤})))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ˡ (≾-⊤ (⊤ · ⊤))))))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (·-monoˡ-≾ (≾-⊤ (⊤ · ⊤))) (≾-⊤ (⊤ · ⊤))))
                (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))))))))


record Eternalᵒ (A : Obj) : Set₁ where

  field

    -- STRUCTURE

    -- The `⟨ ⊤ ⟩`-algebra: this is the only thing a model supplies.

    α : ⟨ ⊤ ⟩ᵒ A →ᵐ A

    -- ALGEBRA LAWS

    α-unit : α ∘ᵐ ⟨⊤⟩-η ≈ᵐ idᵐ

    α-assoc : α ∘ᵐ ⟨⊤⟩-μ ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ α

  -- THE GRADED EXTRACTION, DERIVED
  --
  -- Extraction at every grade (generalises `εᵘ`); consumed by `var`. Relax the
  -- grade up to `⊤`, then run the algebra.

  extᵉ : ∀ {ρ} → ⟨ ρ ⟩ᵒ A →ᵐ A
  extᵉ {ρ} = α ∘ᵐ ⟨⟩-≤ (≾-⊤ ρ)

  -- Extraction is uniform in the grade (compatible with `⟨⟩-≤`): this is what
  -- makes a variable of eternal type interpretable independently of how much
  -- its context has been relaxed. Merge the two relaxations, then use that `≾`
  -- is proof-irrelevant.

  extᵉ-≤ : ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
         → extᵉ {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ extᵉ {ρ₁}
  extᵉ-≤ {ρ₁} {ρ₂} p =
    ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-trans p (≾-⊤ ρ₂)))
              (∘ᵐ-congʳ (⟨⟩-≤-irr _ (≾-⊤ ρ₁))))

  -- At the unit grade the extraction is exactly the possibility counit `εᵘ`:
  -- two maps out of `⟨ u ⟩ᵒ A` agreeing after `η` are equal, `η` and `εᵘ` being
  -- mutually inverse, and after `η` the unit law applies.

  extᵉ-u : extᵉ {u} ≈ᵐ εᵘ
  extᵉ-u =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-assoc _ _ _) α-unit))
              (∘ᵐ-identityˡ εᵘ))))

  -- Extracting from a nested possibility agrees with folding the two layers
  -- with `μ` and extracting once (the `⟨_⟩`-algebra multiplication law):
  -- transport the two relaxations across `μ` (`μ-≤ˡ`, `μ-≤ʳ`) and fold them
  -- into one, which is where `α-assoc` applies.

  extᵉ-μ : ∀ {ρ₁ ρ₂}
         → extᵉ {ρ₂ · ρ₁} ∘ᵐ μ {A} {ρ₁} {ρ₂}
         ≈ᵐ extᵉ {ρ₁} ∘ᵐ ⟨ ρ₁ ⟩ᶠ (extᵉ {ρ₂})
  extᵉ-μ {ρ₁} {ρ₂} = ≈ᵐ-sym
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-∘ᵐ α (⟨⟩-≤ (≾-⊤ ρ₂))))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-nat α (≾-⊤ ρ₁)))))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym α-assoc))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ inner)
              (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))))))
    where
      inner : (⟨⟩-≤ (≾-⊤ (⊤ · ⊤)) ∘ᵐ μ {A} {⊤} {⊤})
                ∘ᵐ (⟨⟩-≤ (≾-⊤ ρ₁) ∘ᵐ ⟨ ρ₁ ⟩ᶠ (⟨⟩-≤ (≾-⊤ ρ₂)))
            ≈ᵐ ⟨⟩-≤ (≾-⊤ (ρ₂ · ρ₁)) ∘ᵐ μ {A} {ρ₁} {ρ₂}
      inner =
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μ-≤ʳ (≾-⊤ ρ₁)))))
        (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (μ-≤ˡ (≾-⊤ ρ₂))))
        (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (·-monoʳ-≾ (≾-⊤ ρ₁)) (≾-⊤ (⊤ · ⊤))))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩-≤-trans (·-monoˡ-≾ (≾-⊤ ρ₂)) _))
                  (∘ᵐ-congˡ (⟨⟩-≤-irr _ (≾-⊤ (ρ₂ · ρ₁))))))))))))

  -- THE BOX COALGEBRA, DERIVED
  --
  -- Necessitation at every grade, as the adjoint mate of `extᵉ` under
  -- `⟨ ρ ⟩ ⊣ [ ρ ]`. This is the `[_]`-coalgebra half of the structure — what
  -- lets an eternal object be carried *under* a box, across the passage of
  -- time.

  necᵉ : ∀ {ρ} → A →ᵐ [ ρ ]ᵒ A
  necᵉ {ρ} = [ ρ ]ᶠ (extᵉ {ρ}) ∘ᵐ η⊣

  -- `necᵉ` is the transpose of `extᵉ`, by definition.

  necᵉ-mate : ∀ {ρ} → necᵉ {ρ} ≈ᵐ [ ρ ]ᶠ (extᵉ {ρ}) ∘ᵐ η⊣
  necᵉ-mate = ≈ᵐ-refl

  -- `extᵉ` and `necᵉ` are adjoint mates (the forward mate direction, from the
  -- left triangle identity and `ε⊣`-naturality).

  extᵉ-mate : ∀ {ρ} → extᵉ {ρ} ≈ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ (necᵉ {ρ})
  extᵉ-mate {ρ} = ≈ᵐ-sym (≈ᵐ-trans
    (∘ᵐ-congʳ (⟨⟩-∘ᵐ ([ ρ ]ᶠ (extᵉ {ρ})) η⊣))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc ε⊣ (⟨ ρ ⟩ᶠ ([ ρ ]ᶠ (extᵉ {ρ}))) (⟨ ρ ⟩ᶠ η⊣)))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat (extᵉ {ρ}))))
    (≈ᵐ-trans (∘ᵐ-assoc (extᵉ {ρ}) ε⊣ (⟨ ρ ⟩ᶠ η⊣))
    (≈ᵐ-trans (∘ᵐ-congʳ triangleˡ)
              (∘ᵐ-identityʳ (extᵉ {ρ})))))))

  -- `necᵉ` is a uniform graded `[_]`-coalgebra:

  -- at the unit grade it is the box's unit `ηᵘ` (from `extᵉ-u`, `η⊣-u`, and
  -- the possibility iso `εᵘ ∘ η ≈ id`).

  necᵉ-u : necᵉ {u} ≈ᵐ ηᵘ
  necᵉ-u =
    ≈ᵐ-trans (∘ᵐ-congʳ η⊣-u)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ η (extᵉ {u}))))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congˡ extᵉ-u)))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ ⟨⟩-εᵘ∘η≡id))
    (≈ᵐ-trans (∘ᵐ-congˡ []-idᵐ)
              (∘ᵐ-identityˡ ηᵘ))))))

  -- it is uniform in the grade (compatible with `[]-≤`; from `[]-≤`/`η⊣`
  -- naturality and `extᵉ-≤`),

  necᵉ-≤ : ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
         → []-≤ p ∘ᵐ necᵉ {ρ₂} ≈ᵐ necᵉ {ρ₁}
  necᵉ-≤ {ρ₁} {ρ₂} p =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat (extᵉ {ρ₂}) p)))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-≤ p))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ (⟨⟩-≤ p) (extᵉ {ρ₂}))))
              (∘ᵐ-congˡ ([]-congᶠ (extᵉ-≤ p))))))))

  -- and it is compatible with the comultiplication `δ`. This is the one
  -- coalgebra law that needs the adjunction's grade-composition coherence,
  -- supplied by the *derived* `η⊣-δ` (itself the future-side transpose of the
  -- primitive counit law `ε⊣-μ`); combined with the algebra law `extᵉ-μ` and
  -- `η⊣`-naturality it reduces to `necᵉ`.

  necᵉ-δ : ∀ {ρ₁ ρ₂}
         → δ ∘ᵐ necᵉ {ρ₁ · ρ₂} ≈ᵐ [ ρ₁ ]ᶠ (necᵉ {ρ₂}) ∘ᵐ necᵉ {ρ₁}
  necᵉ-δ {ρ₁} {ρ₂} =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-δ-nat (extᵉ {ρ₁ · ρ₂}))))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ η⊣-δ)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ inner))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
              (∘ᵐ-assoc _ _ _))))))))
    where
      -- `[ρ₂]ᶠ extᵉ ∘ ([ρ₂]ᶠ μ ∘ η⊣) ≈ necᵉ{ρ₂} ∘ extᵉ{ρ₁}`, from `extᵉ-μ`
      -- and `η⊣`-naturality (the eternal value slides out of the transpose).
      inner : [ ρ₂ ]ᶠ (extᵉ {ρ₁ · ρ₂}) ∘ᵐ ([ ρ₂ ]ᶠ (μ {A} {ρ₂} {ρ₁}) ∘ᵐ η⊣)
            ≈ᵐ necᵉ {ρ₂} ∘ᵐ extᵉ {ρ₁}
      inner =
        ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
        (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ extᵉ-μ))
        (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (extᵉ {ρ₁})))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))


-- THE FREE ALGEBRA
--
-- `⟨ ⊤ ⟩ᵒ X` is eternal for any `X`, with the monad multiplication as its
-- algebra: the two laws *are* the monad's unit and associativity laws.

⟨⊤⟩-eternalᵒ : (X : Obj) → Eternalᵒ (⟨ ⊤ ⟩ᵒ X)
⟨⊤⟩-eternalᵒ X = record { α = ⟨⊤⟩-μ ; α-unit = ⟨⊤⟩-μ∘η≡id ; α-assoc = ⟨⊤⟩-μ∘μ≡μ∘Tμ }

-- `⟨ ⊤ ⟩ᶠ f` is a morphism of free algebras: it commutes with the graded
-- extraction at every grade. From `⟨⟩-≤`- and `⟨⊤⟩-μ`-naturality; the free
-- algebra is the only case where this holds for an arbitrary `f`, `extᵉ`
-- having no naturality law in general.

⟨⊤⟩-free-extᵉ-nat : ∀ {X Y} → (f : X →ᵐ Y) → ∀ {ρ}
                  → Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ Y) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟨ ⊤ ⟩ᶠ f)
                  ≈ᵐ ⟨ ⊤ ⟩ᶠ f ∘ᵐ Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ X) {ρ}
⟨⊤⟩-free-extᵉ-nat f {ρ} =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat (⟨ ⊤ ⟩ᶠ f) (≾-⊤ ρ))))
  (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (⟨⊤⟩-μ-nat f)))
            (∘ᵐ-assoc _ _ _))))

-- Its `[_]`-mate: `⟨ ⊤ ⟩ᶠ f` is also a morphism of the derived box coalgebras.
-- This is the coalgebra-morphism premise a handler fold's parameter-naturality
-- needs, at an arbitrary `f`.

⟨⊤⟩-free-necᵉ-nat : ∀ {X Y} → (f : X →ᵐ Y) → ∀ {ρ}
                  → [ ρ ]ᶠ (⟨ ⊤ ⟩ᶠ f) ∘ᵐ Eternalᵒ.necᵉ (⟨⊤⟩-eternalᵒ X) {ρ}
                  ≈ᵐ Eternalᵒ.necᵉ (⟨⊤⟩-eternalᵒ Y) {ρ} ∘ᵐ ⟨ ⊤ ⟩ᶠ f
⟨⊤⟩-free-necᵉ-nat f =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (≈ᵐ-sym (⟨⊤⟩-free-extᵉ-nat f))))
  (≈ᵐ-trans (∘ᵐ-congˡ ([]-∘ᵐ _ _))
  (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ (η⊣-nat (⟨ ⊤ ⟩ᶠ f)))
            (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))))


-- THE FREE ALGEBRA'S UNIVERSAL PROPERTY, GENERALISED
--
-- `⟨⊤⟩-free-extᵉ-nat`/`⟨⊤⟩-free-necᵉ-nat` above only cover a map already of
-- shape `⟨ ⊤ ⟩ᶠ f`. These generalise to any `g : X →ᵐ ⟨ ⊤ ⟩ᵒ Y`: the algebra
-- morphism `⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ ⟩ᶠ g` its universal property produces still commutes
-- with extraction, hence with necessitation, at every grade.

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

-- Commutes with extraction at every grade.

free-extᵉ-nat : ∀ {X Y} → (g : X →ᵐ ⟨ ⊤ ⟩ᵒ Y) → ∀ {ρ}
              → (⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ ⟩ᶠ g) ∘ᵐ Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ X) {ρ}
              ≈ᵐ Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ Y) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ ⟩ᶠ g)
free-extᵉ-nat g {ρ} =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⊤⟩-μ-nat g))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ⟨⊤⟩-μ∘μ≡μ∘Tμ
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
  ∙ ∘ᵐ-congʳ (⟨⟩-≤-nat _ (≾-⊤ ρ))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- Its `[_]`-mate: commutes with necessitation at every grade.

free-necᵉ-nat : ∀ {X Y} → (f : ⟨ ⊤ ⟩ᵒ X →ᵐ ⟨ ⊤ ⟩ᵒ Y)
              → (∀ {ρ} → f ∘ᵐ Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ X) {ρ}
                       ≈ᵐ Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ Y) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ f)
              → ∀ {ρ} → [ ρ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ (⟨⊤⟩-eternalᵒ X) {ρ}
                      ≈ᵐ Eternalᵒ.necᵉ (⟨⊤⟩-eternalᵒ Y) {ρ} ∘ᵐ f
free-necᵉ-nat f nat =
    ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ nat)
  ∙ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (η⊣-nat f)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- A lock composed before the barrier relaxation is the free algebra's own
-- multiplication applied to the inner relaxation (`⊤` is greatest).

barrier-μ : ∀ {X ρ} → (p : ρ · ⊤ ≾ ⊤)
          → ⟨⟩-≤ p ∘ᵐ μ {X} {⊤} {ρ}
          ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨⟩-≤ (≾-⊤ ρ))
barrier-μ {X} {ρ} p =
    ∘ᵐ-congˡ (⟨⟩-≤-irr p (≾-trans (·-monoˡ-≾ (≾-⊤ ρ)) (≾-⊤ (⊤ · ⊤))))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-trans (·-monoˡ-≾ (≾-⊤ ρ)) (≾-⊤ (⊤ · ⊤))))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (μ-≤ˡ (≾-⊤ ρ))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- Extraction at a lock, applied to the barrier, is the lock's relaxation to
-- `⊤`.

barrier-lock : ∀ {X ρ}
             → Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ X) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (⟨⊤⟩-η {X})
             ≈ᵐ ⟨⟩-≤ (≾-⊤ ρ)
barrier-lock {X} {ρ} =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat ⟨⊤⟩-η (≾-⊤ ρ)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ⟨⊤⟩-μ∘Tη≡id
  ∙ ∘ᵐ-identityˡ _


-- PRODUCTS OF ETERNAL OBJECTS
--
-- Eilenberg–Moore algebras are closed under the category's products, the
-- structure map being assembled componentwise. Both laws reduce componentwise
-- through `⟨⊤⟩-η`- and `⟨⊤⟩-μ`-naturality; no strength is involved.

module _ {A B : Obj} (eA : Eternalᵒ A) (eB : Eternalᵒ B) where

  private
    module EA = Eternalᵒ eA
    module EB = Eternalᵒ eB

    α× : ⟨ ⊤ ⟩ᵒ (A ×ᵐ B) →ᵐ A ×ᵐ B
    α× = ⟨ EA.α ∘ᵐ ⟨ ⊤ ⟩ᶠ fstᵐ , EB.α ∘ᵐ ⟨ ⊤ ⟩ᶠ sndᵐ ⟩ᵐ

    -- two maps into a product agree iff they agree componentwise
    ×-ext : ∀ {X} {f g : X →ᵐ A ×ᵐ B}
          → fstᵐ ∘ᵐ f ≈ᵐ fstᵐ ∘ᵐ g → sndᵐ ∘ᵐ f ≈ᵐ sndᵐ ∘ᵐ g → f ≈ᵐ g
    ×-ext {f = f} {g} p q =
      ≈ᵐ-trans (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ f) (sndᵐ ∘ᵐ f) f ≈ᵐ-refl ≈ᵐ-refl)
               (≈ᵐ-sym (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ f) (sndᵐ ∘ᵐ f) g (≈ᵐ-sym p) (≈ᵐ-sym q)))

    -- the componentwise unit step
    unit-comp : ∀ {C} → (α : ⟨ ⊤ ⟩ᵒ C →ᵐ C) → (α ∘ᵐ ⟨⊤⟩-η ≈ᵐ idᵐ)
              → (π : A ×ᵐ B →ᵐ C)
              → (α ∘ᵐ ⟨ ⊤ ⟩ᶠ π) ∘ᵐ ⟨⊤⟩-η ≈ᵐ π
    unit-comp α αu π =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⊤⟩-η-nat π))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ αu) (∘ᵐ-identityˡ π))))

    -- the two sides of the associativity law, one component at a time
    assoc-lhs : ∀ {C} → (α : ⟨ ⊤ ⟩ᵒ C →ᵐ C)
              → (α ∘ᵐ ⟨⊤⟩-μ ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ α)
              → (π : A ×ᵐ B →ᵐ C)
              → (π ∘ᵐ α× ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ π)
              → π ∘ᵐ (α× ∘ᵐ ⟨⊤⟩-μ) ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ (α ∘ᵐ ⟨ ⊤ ⟩ᶠ π)
    assoc-lhs α αa π pf =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc π α× ⟨⊤⟩-μ))
      (≈ᵐ-trans (∘ᵐ-congˡ pf)
      (≈ᵐ-trans (∘ᵐ-assoc α (⟨ ⊤ ⟩ᶠ π) ⟨⊤⟩-μ)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⊤⟩-μ-nat π))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc α ⟨⊤⟩-μ (⟨ ⊤ ⟩ᶠ (⟨ ⊤ ⟩ᶠ π))))
      (≈ᵐ-trans (∘ᵐ-congˡ αa)
      (≈ᵐ-trans (∘ᵐ-assoc α (⟨ ⊤ ⟩ᶠ α) (⟨ ⊤ ⟩ᶠ (⟨ ⊤ ⟩ᶠ π)))
                (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ α (⟨ ⊤ ⟩ᶠ π))))))))))

    assoc-rhs : ∀ {C} → (α : ⟨ ⊤ ⟩ᵒ C →ᵐ C)
              → (π : A ×ᵐ B →ᵐ C)
              → (π ∘ᵐ α× ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ π)
              → π ∘ᵐ (α× ∘ᵐ ⟨ ⊤ ⟩ᶠ α×) ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ (α ∘ᵐ ⟨ ⊤ ⟩ᶠ π)
    assoc-rhs α π pf =
      ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc π α× (⟨ ⊤ ⟩ᶠ α×)))
      (≈ᵐ-trans (∘ᵐ-congˡ pf)
      (≈ᵐ-trans (∘ᵐ-assoc α (⟨ ⊤ ⟩ᶠ π) (⟨ ⊤ ⟩ᶠ α×))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ π α×)))
                (∘ᵐ-congʳ (⟨⟩-congᶠ pf)))))

    pfˡ : fstᵐ ∘ᵐ α× ≈ᵐ EA.α ∘ᵐ ⟨ ⊤ ⟩ᶠ fstᵐ
    pfˡ = ⟨⟩ᵐ-fstᵐ _ _

    pfʳ : sndᵐ ∘ᵐ α× ≈ᵐ EB.α ∘ᵐ ⟨ ⊤ ⟩ᶠ sndᵐ
    pfʳ = ⟨⟩ᵐ-sndᵐ _ _

  ×ᵐ-eternalᵒ : Eternalᵒ (A ×ᵐ B)
  ×ᵐ-eternalᵒ = record
    { α = α×
    ; α-unit = ×-ext
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ pfˡ)
        (≈ᵐ-trans (unit-comp EA.α EA.α-unit fstᵐ)
                  (≈ᵐ-sym (∘ᵐ-identityʳ fstᵐ)))))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ pfʳ)
        (≈ᵐ-trans (unit-comp EB.α EB.α-unit sndᵐ)
                  (≈ᵐ-sym (∘ᵐ-identityʳ sndᵐ)))))
    ; α-assoc = ×-ext
        (≈ᵐ-trans (assoc-lhs EA.α EA.α-assoc fstᵐ pfˡ)
                  (≈ᵐ-sym (assoc-rhs EA.α fstᵐ pfˡ)))
        (≈ᵐ-trans (assoc-lhs EB.α EB.α-assoc sndᵐ pfʳ)
                  (≈ᵐ-sym (assoc-rhs EB.α sndᵐ pfʳ)))
    }

  -- The product's extraction acts componentwise at every grade: the relaxation
  -- to `⊤` slides past the projection (`⟨⟩-≤-nat`), leaving the factor's own
  -- extraction.

  ×ᵐ-eternalᵒ-extᵉ : ∀ {ρ} → Eternalᵒ.extᵉ ×ᵐ-eternalᵒ {ρ}
                   ≈ᵐ ⟨ Eternalᵒ.extᵉ eA ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ
                      , Eternalᵒ.extᵉ eB ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ⟩ᵐ
  ×ᵐ-eternalᵒ-extᵉ {ρ} = ⟨⟩ᵐ-unique _ _ _ (comp EA.α fstᵐ pfˡ) (comp EB.α sndᵐ pfʳ)
    where
      comp : ∀ {C} → (α : ⟨ ⊤ ⟩ᵒ C →ᵐ C) → (π : A ×ᵐ B →ᵐ C)
           → (π ∘ᵐ α× ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ π)
           → π ∘ᵐ Eternalᵒ.extᵉ ×ᵐ-eternalᵒ {ρ}
             ≈ᵐ (α ∘ᵐ ⟨⟩-≤ (≾-⊤ ρ)) ∘ᵐ ⟨ ρ ⟩ᶠ π
      comp α π pf =
        ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        (≈ᵐ-trans (∘ᵐ-congˡ pf)
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-nat π (≾-⊤ ρ)))
                  (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))


-- ETERNALITY TRANSPORTS ALONG AN ISOMORPHISM
--
-- Being eternal is invariant under isomorphism: conjugating the algebra by an
-- iso preserves both laws.

module _ {A B : Obj} (f : A →ᵐ B) (g : B →ᵐ A)
         (fg : f ∘ᵐ g ≈ᵐ idᵐ) (gf : g ∘ᵐ f ≈ᵐ idᵐ)
         (eA : Eternalᵒ A) where

  private
    module EA = Eternalᵒ eA

    α' : ⟨ ⊤ ⟩ᵒ B →ᵐ B
    α' = f ∘ᵐ EA.α ∘ᵐ ⟨ ⊤ ⟩ᶠ g

    -- the conjugated algebra applied to a `⟨ ⊤ ⟩`-layer of `g`s
    conj : ⟨ ⊤ ⟩ᵒ (⟨ ⊤ ⟩ᵒ B) →ᵐ B
    conj = f ∘ᵐ EA.α ∘ᵐ ⟨ ⊤ ⟩ᶠ (EA.α ∘ᵐ ⟨ ⊤ ⟩ᶠ g)

    unit : α' ∘ᵐ ⟨⊤⟩-η ≈ᵐ idᵐ
    unit =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⊤⟩-η-nat g)))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ EA.α-unit))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-identityˡ _)) fg)))))

    assocˡ : α' ∘ᵐ ⟨⊤⟩-μ ≈ᵐ conj
    assocˡ =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⊤⟩-μ-nat g)))
      (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congˡ EA.α-assoc))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
                (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))))))))

    assocʳ : α' ∘ᵐ ⟨ ⊤ ⟩ᶠ α' ≈ᵐ conj
    assocʳ =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ g α'))))
                (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-congᶠ
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc g f _))
        (≈ᵐ-trans (∘ᵐ-congˡ gf) (∘ᵐ-identityˡ _))))))))

  iso-eternalᵒ : Eternalᵒ B
  iso-eternalᵒ = record
    { α       = α'
    ; α-unit  = unit
    ; α-assoc = ≈ᵐ-trans assocˡ (≈ᵐ-sym assocʳ)
    }

  -- Its extraction, unfolded: relax into the algebra's grade underneath the
  -- iso, i.e. conjugate the original extraction.

  iso-eternalᵒ-extᵉ : ∀ {ρ} → Eternalᵒ.extᵉ iso-eternalᵒ {ρ}
                    ≈ᵐ f ∘ᵐ Eternalᵒ.extᵉ eA {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ g
  iso-eternalᵒ-extᵉ {ρ} =
    ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-≤-nat g (≾-⊤ ρ))))
              (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))


-- UNIT-EQUIVALENT GRADES
--
-- At a grade `ρ` that is ≾-equivalent to the unit, `⟨ ρ ⟩ᵒ` is isomorphic to
-- the identity: `η` relaxed up to `ρ`, and `εᵘ` relaxed down from it, are
-- mutually inverse. So `⟨ ρ ⟩ᵒ A` is eternal whenever `A` is, which is what
-- makes a lock at such a grade admissible inside an eternal context.

⟨u≈⟩-unit : ∀ {A ρ} → u ≾ ρ → A →ᵐ ⟨ ρ ⟩ᵒ A
⟨u≈⟩-unit q = ⟨⟩-≤ q ∘ᵐ η

⟨u≈⟩-counit : ∀ {A ρ} → ρ ≾ u → ⟨ ρ ⟩ᵒ A →ᵐ A
⟨u≈⟩-counit p = εᵘ ∘ᵐ ⟨⟩-≤ p

⟨u≈⟩-counit-unit : ∀ {A ρ} → (q : u ≾ ρ) → (p : ρ ≾ u)
                 → ⟨u≈⟩-counit {A} p ∘ᵐ ⟨u≈⟩-unit q ≈ᵐ idᵐ
⟨u≈⟩-counit-unit q p =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ
     (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
               (≈ᵐ-trans (∘ᵐ-congˡ
               (≈ᵐ-trans (⟨⟩-≤-trans q p)
                    (≈ᵐ-trans (⟨⟩-≤-irr _ ≾-refl)
                              (⟨⟩-≤-refl))))
                         (∘ᵐ-identityˡ _))))
            (⟨⟩-εᵘ∘η≡id))

⟨u≈⟩-unit-counit : ∀ {A ρ} → (q : u ≾ ρ) → (p : ρ ≾ u)
                 → ⟨u≈⟩-unit {A} q ∘ᵐ ⟨u≈⟩-counit p ≈ᵐ idᵐ
⟨u≈⟩-unit-counit q p =
  ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
  (≈ᵐ-trans (∘ᵐ-congʳ
     (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
               (≈ᵐ-trans (∘ᵐ-congˡ ⟨⟩-η∘εᵘ≡id)
                         (∘ᵐ-identityˡ _))))
  (≈ᵐ-trans (⟨⟩-≤-trans p q)
  (≈ᵐ-trans (⟨⟩-≤-irr _ ≾-refl)
            (⟨⟩-≤-refl))))

⟨u≈⟩-eternalᵒ : ∀ {A ρ} → (q : u ≾ ρ) → (p : ρ ≾ u)
              → Eternalᵒ A → Eternalᵒ (⟨ ρ ⟩ᵒ A)
⟨u≈⟩-eternalᵒ q p =
  iso-eternalᵒ (⟨u≈⟩-unit q) (⟨u≈⟩-counit p)
    (⟨u≈⟩-unit-counit q p) (⟨u≈⟩-counit-unit q p)

-- Its extraction, unfolded: relax into the lock pointwise, extract underneath,
-- relax back out.

⟨u≈⟩-eternalᵒ-extᵉ : ∀ {A ρ σ} → (q : u ≾ ρ) → (p : ρ ≾ u) → (eA : Eternalᵒ A)
                   → Eternalᵒ.extᵉ (⟨u≈⟩-eternalᵒ q p eA) {σ}
                   ≈ᵐ ⟨u≈⟩-unit q ∘ᵐ Eternalᵒ.extᵉ eA {σ}
                        ∘ᵐ ⟨ σ ⟩ᶠ (⟨u≈⟩-counit p)
⟨u≈⟩-eternalᵒ-extᵉ q p eA =
  iso-eternalᵒ-extᵉ (⟨u≈⟩-unit q) (⟨u≈⟩-counit p)
    (⟨u≈⟩-unit-counit q p) (⟨u≈⟩-counit-unit q p) eA
