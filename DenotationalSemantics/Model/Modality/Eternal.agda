------------------------------------------------------------------------
-- Objects interpreting *eternal* types.                                --
--                                                                      --
-- An eternal type (`Syntax.Types.Eternal`) is available at any         --
-- grade, not only below the unit `u`; concretely (`Example.PSh`)       --
-- these are the constant presheaves.                                   --
--                                                                      --
-- `Eternalᵒ A` is an Eilenberg–Moore algebra `α : ⟨ ⊤ ⟩ᵒ A →ᵐ A`       --
-- for the monad `⟨⊤⟩` the context modality collapses to at the         --
-- greatest grade `⊤`. Extraction `extᵉ`, necessitation `necᵉ`, and     --
-- their laws are all derived from `α`; a model supplies only the       --
-- algebra.                                                             --
--                                                                      --
-- An isomorphism `A ≅ [ ρ ]ᵒ A` would be too strong; the algebra       --
-- needs no seriality assumption.                                       --
------------------------------------------------------------------------

open import Syntax.Durations using (Duration)
open import Syntax.Grades

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction

module DenotationalSemantics.Model.Modality.Eternal
         (Cat : Category)
         {D : Duration} (G : Grade D)
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

-- At the greatest grade the graded context modality collapses to an ordinary
-- monad: `≾-⊤` relaxes the grades `u` and `⊤ · ⊤` produced by `η` and `μ` back
-- to `⊤`. `⊤` is not assumed absorbing.

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

-- Left unit.

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

-- Right unit.

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

-- Associativity.

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

  -- Extraction at every grade, generalising `εᵘ`; consumed by `var`.

  extᵉ : ∀ {ρ} → ⟨ ρ ⟩ᵒ A →ᵐ A
  extᵉ {ρ} = α ∘ᵐ ⟨⟩-≤ (≾-⊤ ρ)

  -- Extraction is uniform in the grade (compatible with `⟨⟩-≤`): this is what
  -- makes a variable of eternal type interpretable independently of how much
  -- its context has been relaxed.

  extᵉ-≤ : ∀ {ρ₁ ρ₂} → (p : ρ₁ ≾ ρ₂)
         → extᵉ {ρ₂} ∘ᵐ ⟨⟩-≤ p ≈ᵐ extᵉ {ρ₁}
  extᵉ-≤ {ρ₁} {ρ₂} p =
    ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩-≤-trans p (≾-⊤ ρ₂)))
              (∘ᵐ-congʳ (⟨⟩-≤-irr _ (≾-⊤ ρ₁))))

  -- At the unit grade, extraction is exactly the possibility counit `εᵘ`.

  extᵉ-u : extᵉ {u} ≈ᵐ εᵘ
  extᵉ-u =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym ⟨⟩-η∘εᵘ≡id))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-trans (∘ᵐ-assoc _ _ _) α-unit))
              (∘ᵐ-identityˡ εᵘ))))

  -- Extracting from a nested possibility agrees with folding the two layers
  -- with `μ` and extracting once (the `⟨_⟩`-algebra multiplication law).

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

  -- Necessitation at every grade, the adjoint mate of `extᵉ` under
  -- `⟨ ρ ⟩ ⊣ [ ρ ]`: the `[_]`-coalgebra half of the structure, letting an
  -- eternal object be carried under a box, across the passage of time.

  necᵉ : ∀ {ρ} → A →ᵐ [ ρ ]ᵒ A
  necᵉ {ρ} = [ ρ ]ᶠ (extᵉ {ρ}) ∘ᵐ η⊣

  -- `necᵉ` is the transpose of `extᵉ`, by definition.

  necᵉ-mate : ∀ {ρ} → necᵉ {ρ} ≈ᵐ [ ρ ]ᶠ (extᵉ {ρ}) ∘ᵐ η⊣
  necᵉ-mate = ≈ᵐ-refl

  -- `extᵉ` and `necᵉ` are adjoint mates.

  extᵉ-mate : ∀ {ρ} → extᵉ {ρ} ≈ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ (necᵉ {ρ})
  extᵉ-mate {ρ} = ≈ᵐ-sym (≈ᵐ-trans
    (∘ᵐ-congʳ (⟨⟩-∘ᵐ ([ ρ ]ᶠ (extᵉ {ρ})) η⊣))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc ε⊣ (⟨ ρ ⟩ᶠ ([ ρ ]ᶠ (extᵉ {ρ}))) (⟨ ρ ⟩ᶠ η⊣)))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat (extᵉ {ρ}))))
    (≈ᵐ-trans (∘ᵐ-assoc (extᵉ {ρ}) ε⊣ (⟨ ρ ⟩ᶠ η⊣))
    (≈ᵐ-trans (∘ᵐ-congʳ triangleˡ)
              (∘ᵐ-identityʳ (extᵉ {ρ})))))))

  -- `necᵉ` is a uniform graded `[_]`-coalgebra.

  -- At the unit grade it is the box's unit `ηᵘ`.

  necᵉ-u : necᵉ {u} ≈ᵐ ηᵘ
  necᵉ-u =
    ≈ᵐ-trans (∘ᵐ-congʳ η⊣-u)
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ η (extᵉ {u}))))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congˡ extᵉ-u)))
    (≈ᵐ-trans (∘ᵐ-congˡ ([]-congᶠ ⟨⟩-εᵘ∘η≡id))
    (≈ᵐ-trans (∘ᵐ-congˡ []-idᵐ)
              (∘ᵐ-identityˡ ηᵘ))))))

  -- It is uniform in the grade (compatible with `[]-≤`).

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

  -- It is compatible with the comultiplication `δ`.

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


-- `⟨ ⊤ ⟩ᵒ X` is eternal for any `X`, with the monad multiplication as its
-- algebra: the two laws *are* the monad's unit and associativity laws.

⟨⊤⟩-eternalᵒ : (X : Obj) → Eternalᵒ (⟨ ⊤ ⟩ᵒ X)
⟨⊤⟩-eternalᵒ X = record { α = ⟨⊤⟩-μ ; α-unit = ⟨⊤⟩-μ∘η≡id ; α-assoc = ⟨⊤⟩-μ∘μ≡μ∘Tμ }

-- `⟨ ⊤ ⟩ᶠ f` is a morphism of free algebras: it commutes with the graded
-- extraction at every grade. The free algebra is the only case where this
-- holds for an arbitrary `f`, `extᵉ` having no naturality law in general.

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


-- Eilenberg–Moore algebras are closed under the category's products, the
-- structure map being assembled componentwise.

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


-- `⟨ ρ ⟩` is a left adjoint, so it preserves the coproduct: a map out of
-- `⟨ ρ ⟩ᵒ (A +ᵐ B)` is determined by its restrictions along the injections.
-- Both directions go through the transpose `[ ρ ]ᶠ f ∘ᵐ η⊣`.

⟨⟩-transpose : ∀ {A C ρ} → (f : ⟨ ρ ⟩ᵒ A →ᵐ C)
             → f ≈ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ ([ ρ ]ᶠ f ∘ᵐ η⊣)
⟨⟩-transpose {ρ = ρ} f = ≈ᵐ-sym
  ( ∘ᵐ-congʳ (⟨⟩-∘ᵐ ([ ρ ]ᶠ f) η⊣)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat f))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ triangleˡ
  ∙ ∘ᵐ-identityʳ f)

⟨⟩-mate-≈ : ∀ {A C ρ} {f g : ⟨ ρ ⟩ᵒ A →ᵐ C}
          → [ ρ ]ᶠ f ∘ᵐ η⊣ ≈ᵐ [ ρ ]ᶠ g ∘ᵐ η⊣ → f ≈ᵐ g
⟨⟩-mate-≈ {f = f} {g} e =
  ⟨⟩-transpose f ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ e) ∙ ≈ᵐ-sym (⟨⟩-transpose g)

⟨⟩-mate-∘ : ∀ {A D C ρ} {f g : ⟨ ρ ⟩ᵒ A →ᵐ C} → (ι : D →ᵐ A)
          → f ∘ᵐ ⟨ ρ ⟩ᶠ ι ≈ᵐ g ∘ᵐ ⟨ ρ ⟩ᶠ ι
          → ([ ρ ]ᶠ f ∘ᵐ η⊣) ∘ᵐ ι ≈ᵐ ([ ρ ]ᶠ g ∘ᵐ η⊣) ∘ᵐ ι
⟨⟩-mate-∘ {f = f} {g} ι e = flat f ∙ ∘ᵐ-congˡ ([]-congᶠ e) ∙ ≈ᵐ-sym (flat g)
  where
    flat : ∀ h → ([ _ ]ᶠ h ∘ᵐ η⊣) ∘ᵐ ι ≈ᵐ [ _ ]ᶠ (h ∘ᵐ ⟨ _ ⟩ᶠ ι) ∘ᵐ η⊣
    flat h =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ι))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))

-- two maps out of a coproduct agree iff they agree on both injections

+-ext : ∀ {A B C} {f g : A +ᵐ B →ᵐ C}
      → f ∘ᵐ inlᵐ ≈ᵐ g ∘ᵐ inlᵐ → f ∘ᵐ inrᵐ ≈ᵐ g ∘ᵐ inrᵐ → f ≈ᵐ g
+-ext {f = f} {g} p q =
    []ᵐ-unique _ _ f ≈ᵐ-refl ≈ᵐ-refl
  ∙ [ p , q ]ᵐ-cong
  ∙ ≈ᵐ-sym ([]ᵐ-unique _ _ g ≈ᵐ-refl ≈ᵐ-refl)

⟨⟩-+-ext : ∀ {A B C ρ} {f g : ⟨ ρ ⟩ᵒ (A +ᵐ B) →ᵐ C}
         → f ∘ᵐ ⟨ ρ ⟩ᶠ inlᵐ ≈ᵐ g ∘ᵐ ⟨ ρ ⟩ᶠ inlᵐ
         → f ∘ᵐ ⟨ ρ ⟩ᶠ inrᵐ ≈ᵐ g ∘ᵐ ⟨ ρ ⟩ᶠ inrᵐ
         → f ≈ᵐ g
⟨⟩-+-ext p q = ⟨⟩-mate-≈ (+-ext (⟨⟩-mate-∘ inlᵐ p) (⟨⟩-mate-∘ inrᵐ q))

-- the same through two layers

⟨⟩²-+-ext : ∀ {A B C ρ₁ ρ₂} {f g : ⟨ ρ₁ ⟩ᵒ (⟨ ρ₂ ⟩ᵒ (A +ᵐ B)) →ᵐ C}
          → f ∘ᵐ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ inlᵐ) ≈ᵐ g ∘ᵐ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ inlᵐ)
          → f ∘ᵐ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ inrᵐ) ≈ᵐ g ∘ᵐ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ inrᵐ)
          → f ≈ᵐ g
⟨⟩²-+-ext p q =
  ⟨⟩-mate-≈ (⟨⟩-+-ext (⟨⟩-mate-∘ (⟨ _ ⟩ᶠ inlᵐ) p) (⟨⟩-mate-∘ (⟨ _ ⟩ᶠ inrᵐ) q))

-- At the greatest grade, extraction is the algebra itself.

extᵉ-⊤ : ∀ {A} → (eA : Eternalᵒ A) → Eternalᵒ.extᵉ eA {⊤} ≈ᵐ Eternalᵒ.α eA
extᵉ-⊤ eA =
    ∘ᵐ-congʳ (⟨⟩-≤-irr _ ≾-refl)
  ∙ ∘ᵐ-congʳ ⟨⟩-≤-refl
  ∙ ∘ᵐ-identityʳ _

-- Eilenberg–Moore algebras are closed under the category's coproducts: the
-- structure map is the transpose of the summands' necessitations, and acts
-- summandwise.

module _ {A B : Obj} (eA : Eternalᵒ A) (eB : Eternalᵒ B) where

  private
    module EA = Eternalᵒ eA
    module EB = Eternalᵒ eB

    α+ : ⟨ ⊤ ⟩ᵒ (A +ᵐ B) →ᵐ A +ᵐ B
    α+ = ε⊣ ∘ᵐ ⟨ ⊤ ⟩ᶠ [ [ ⊤ ]ᶠ inlᵐ ∘ᵐ EA.necᵉ {⊤} , [ ⊤ ]ᶠ inrᵐ ∘ᵐ EB.necᵉ {⊤} ]ᵐ

    -- on one summand, given its injection's copairing law
    summand : ∀ {X} (eX : Eternalᵒ X) (ι : X →ᵐ A +ᵐ B)
            → [ [ ⊤ ]ᶠ inlᵐ ∘ᵐ EA.necᵉ {⊤} , [ ⊤ ]ᶠ inrᵐ ∘ᵐ EB.necᵉ {⊤} ]ᵐ ∘ᵐ ι
              ≈ᵐ [ ⊤ ]ᶠ ι ∘ᵐ Eternalᵒ.necᵉ eX {⊤}
            → α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ ι ≈ᵐ ι ∘ᵐ Eternalᵒ.α eX
    summand eX ι e =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ e)
      ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat ι))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (Eternalᵒ.extᵉ-mate eX))
      ∙ ∘ᵐ-congʳ (extᵉ-⊤ eX)

    pfˡ : α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ inlᵐ ≈ᵐ inlᵐ ∘ᵐ EA.α
    pfˡ = summand eA inlᵐ ([]ᵐ-inlᵐ _ _)

    pfʳ : α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ inrᵐ ≈ᵐ inrᵐ ∘ᵐ EB.α
    pfʳ = summand eB inrᵐ ([]ᵐ-inrᵐ _ _)

    unit-side : ∀ {X} (ι : X →ᵐ A +ᵐ B) (α : ⟨ ⊤ ⟩ᵒ X →ᵐ X)
              → α ∘ᵐ ⟨⊤⟩-η ≈ᵐ idᵐ → α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ ι ≈ᵐ ι ∘ᵐ α
              → (α+ ∘ᵐ ⟨⊤⟩-η) ∘ᵐ ι ≈ᵐ idᵐ ∘ᵐ ι
    unit-side ι α αu pf =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⊤⟩-η-nat ι))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ pf
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ αu
      ∙ ∘ᵐ-identityʳ ι
      ∙ ≈ᵐ-sym (∘ᵐ-identityˡ ι)

    assoc-side : ∀ {X} (ι : X →ᵐ A +ᵐ B) (α : ⟨ ⊤ ⟩ᵒ X →ᵐ X)
               → α ∘ᵐ ⟨⊤⟩-μ ≈ᵐ α ∘ᵐ ⟨ ⊤ ⟩ᶠ α → α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ ι ≈ᵐ ι ∘ᵐ α
               → (α+ ∘ᵐ ⟨⊤⟩-μ) ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨ ⊤ ⟩ᶠ ι)
                 ≈ᵐ (α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ α+) ∘ᵐ ⟨ ⊤ ⟩ᶠ (⟨ ⊤ ⟩ᶠ ι)
    assoc-side ι α αa pf =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⊤⟩-μ-nat ι))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ pf
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ αa
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym pf)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (≈ᵐ-sym pf))
      ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

  +ᵐ-eternalᵒ : Eternalᵒ (A +ᵐ B)
  +ᵐ-eternalᵒ = record
    { α       = α+
    ; α-unit  = +-ext (unit-side inlᵐ EA.α EA.α-unit pfˡ)
                      (unit-side inrᵐ EB.α EB.α-unit pfʳ)
    ; α-assoc = ⟨⟩²-+-ext (assoc-side inlᵐ EA.α EA.α-assoc pfˡ)
                          (assoc-side inrᵐ EB.α EB.α-assoc pfʳ)
    }

  -- The coproduct's extraction acts summandwise at every grade.

  private
    ext-side : ∀ {X ρ} (ι : X →ᵐ A +ᵐ B) (α : ⟨ ⊤ ⟩ᵒ X →ᵐ X)
             → α+ ∘ᵐ ⟨ ⊤ ⟩ᶠ ι ≈ᵐ ι ∘ᵐ α
             → Eternalᵒ.extᵉ +ᵐ-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ι
               ≈ᵐ ι ∘ᵐ (α ∘ᵐ ⟨⟩-≤ (≾-⊤ ρ))
    ext-side {ρ = ρ} ι α pf =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-≤-nat ι (≾-⊤ ρ)))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ pf
      ∙ ∘ᵐ-assoc _ _ _

  +ᵐ-eternalᵒ-inl : ∀ {ρ} → Eternalᵒ.extᵉ +ᵐ-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ inlᵐ
                          ≈ᵐ inlᵐ ∘ᵐ Eternalᵒ.extᵉ eA {ρ}
  +ᵐ-eternalᵒ-inl = ext-side inlᵐ EA.α pfˡ

  +ᵐ-eternalᵒ-inr : ∀ {ρ} → Eternalᵒ.extᵉ +ᵐ-eternalᵒ {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ inrᵐ
                          ≈ᵐ inrᵐ ∘ᵐ Eternalᵒ.extᵉ eB {ρ}
  +ᵐ-eternalᵒ-inr = ext-side inrᵐ EB.α pfʳ


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

  iso-eternalᵒ-extᵉ : ∀ {ρ} → Eternalᵒ.extᵉ iso-eternalᵒ {ρ}
                    ≈ᵐ f ∘ᵐ Eternalᵒ.extᵉ eA {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ g
  iso-eternalᵒ-extᵉ {ρ} =
    ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-congʳ (⟨⟩-≤-nat g (≾-⊤ ρ))))
              (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))


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

⟨u≈⟩-eternalᵒ-extᵉ : ∀ {A ρ σ} → (q : u ≾ ρ) → (p : ρ ≾ u) → (eA : Eternalᵒ A)
                   → Eternalᵒ.extᵉ (⟨u≈⟩-eternalᵒ q p eA) {σ}
                   ≈ᵐ ⟨u≈⟩-unit q ∘ᵐ Eternalᵒ.extᵉ eA {σ}
                        ∘ᵐ ⟨ σ ⟩ᶠ (⟨u≈⟩-counit p)
⟨u≈⟩-eternalᵒ-extᵉ q p eA =
  iso-eternalᵒ-extᵉ (⟨u≈⟩-unit q) (⟨u≈⟩-counit p)
    (⟨u≈⟩-unit-counit q p) (⟨u≈⟩-counit-unit q p) eA
