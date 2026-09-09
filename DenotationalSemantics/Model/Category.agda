------------------------------------------------------------------------
-- Setoid-enriched cartesian closed category structure for the models   --
-- of the language.                                                     --
--                                                                    --
-- Each hom-set carries an equivalence relation `_≈ᵐ_` of morphism       --
-- equality, and every equational law is stated up to `_≈ᵐ_`. This is    --
-- what lets the context (possibility) modality be realised as a coend    --
-- (a quotient), whose morphism equality is coarser than propositional    --
-- equality.                                                            --
--                                                                    --
-- Beyond the core (identities, composition, and its congruence) we      --
-- record the cartesian closed structure (terminal, initial, binary       --
-- products, exponentials) with the congruences needed to reason up to    --
-- `_≈ᵐ_`.                                                              --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Category where

open import Util.Equality

record Category : Set₂ where

  -- OBJECTS AND MORPHISMS

  field
    Obj : Set₁

    _→ᵐ_ : (A B : Obj) → Set₀

  infix 20 _→ᵐ_

  -- MORPHISM EQUALITY (a setoid on each hom-set)

  field
    _≈ᵐ_ : ∀ {A B} → (f g : A →ᵐ B) → Set₀

    ≈ᵐ-refl  : ∀ {A B} {f : A →ᵐ B} → f ≈ᵐ f
    ≈ᵐ-sym   : ∀ {A B} {f g : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ f
    ≈ᵐ-trans : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h

  infix 4 _≈ᵐ_

  -- IDENTITIES AND COMPOSITION

  field
    idᵐ : ∀ {A} → A →ᵐ A
    _∘ᵐ_ : ∀ {A B C} → B →ᵐ C → A →ᵐ B → A →ᵐ C

    ∘ᵐ-congˡ : ∀ {A B C} {g g' : B →ᵐ C} {f : A →ᵐ B}
             → g ≈ᵐ g' → g ∘ᵐ f ≈ᵐ g' ∘ᵐ f
    ∘ᵐ-congʳ : ∀ {A B C} {g : B →ᵐ C} {f f' : A →ᵐ B}
             → f ≈ᵐ f' → g ∘ᵐ f ≈ᵐ g ∘ᵐ f'

    ∘ᵐ-identityˡ : ∀ {A B} → (f : A →ᵐ B) → idᵐ ∘ᵐ f ≈ᵐ f
    ∘ᵐ-identityʳ : ∀ {A B} → (f : A →ᵐ B) → f ∘ᵐ idᵐ ≈ᵐ f
    ∘ᵐ-assoc : ∀ {A B C D} → (h : C →ᵐ D) → (g : B →ᵐ C) → (f : A →ᵐ B)
             → (h ∘ᵐ g) ∘ᵐ f ≈ᵐ h ∘ᵐ (g ∘ᵐ f)

  infixr 9 _∘ᵐ_

  -- two-sided congruence of composition, derived from the one-sided ones

  ∘ᵐ-cong : ∀ {A B C} {g g' : B →ᵐ C} {f f' : A →ᵐ B}
          → g ≈ᵐ g' → f ≈ᵐ f' → g ∘ᵐ f ≈ᵐ g' ∘ᵐ f'
  ∘ᵐ-cong q p = ≈ᵐ-trans (∘ᵐ-congˡ q) (∘ᵐ-congʳ p)

  -- propositional equality of morphisms implies categorical equality

  ≡→≈ᵐ : ∀ {A B} {f g : A →ᵐ B} → f ≡ g → f ≈ᵐ g
  ≡→≈ᵐ {f = f} e = subst (λ h → f ≈ᵐ h) e ≈ᵐ-refl

  -- TERMINAL OBJECT

  field
    𝟙ᵐ : Obj

    terminalᵐ : ∀ {A} → A →ᵐ 𝟙ᵐ
    terminalᵐ-unique : ∀ {A} {f : A →ᵐ 𝟙ᵐ} → f ≈ᵐ terminalᵐ

  -- INITIAL OBJECT

  field
    𝟘ᵐ : Obj

    initialᵐ : ∀ {A} → 𝟘ᵐ →ᵐ A
    initialᵐ-unique : ∀ {A} {f : 𝟘ᵐ →ᵐ A} → f ≈ᵐ initialᵐ

    -- The initial object is *strict*: an object admitting a map to `𝟘ᵐ` is
    -- itself initial, so any two maps out of it agree. This is what the
    -- calculus's eta rule for `absurd` needs — with an empty-typed value in
    -- scope, every computation of the same type is the same one — and
    -- `initialᵐ-unique` alone does not give it, since that only speaks about
    -- maps *out of* `𝟘ᵐ`.

    𝟘ᵐ-strict : ∀ {X A} → X →ᵐ 𝟘ᵐ → (f g : X →ᵐ A) → f ≈ᵐ g

  -- BINARY PRODUCTS

  field
    _×ᵐ_ : Obj → Obj → Obj

    fstᵐ : ∀ {A B} → A ×ᵐ B →ᵐ A
    sndᵐ : ∀ {A B} → A ×ᵐ B →ᵐ B
    ⟨_,_⟩ᵐ : ∀ {A B C} → A →ᵐ B → A →ᵐ C → A →ᵐ B ×ᵐ C

    ⟨_,_⟩ᵐ-cong : ∀ {A B C} {f f' : A →ᵐ B} {g g' : A →ᵐ C}
                → f ≈ᵐ f' → g ≈ᵐ g' → ⟨ f , g ⟩ᵐ ≈ᵐ ⟨ f' , g' ⟩ᵐ

    ⟨⟩ᵐ-fstᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → fstᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≈ᵐ f
    ⟨⟩ᵐ-sndᵐ : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → sndᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≈ᵐ g
    ⟨⟩ᵐ-unique : ∀ {A B C} → (f : A →ᵐ B) → (g : A →ᵐ C) → (h : A →ᵐ B ×ᵐ C)
               → fstᵐ ∘ᵐ h ≈ᵐ f → sndᵐ ∘ᵐ h ≈ᵐ g → h ≈ᵐ ⟨ f , g ⟩ᵐ

  infixr 23 _×ᵐ_

  -- functorial action of the product

  mapˣᵐ : ∀ {A B C D} → A →ᵐ C → B →ᵐ D → A ×ᵐ B →ᵐ C ×ᵐ D
  mapˣᵐ f g = ⟨ f ∘ᵐ fstᵐ , g ∘ᵐ sndᵐ ⟩ᵐ

  -- the product functor preserves identities

  mapˣᵐ-idᵐ : ∀ {A B} → mapˣᵐ (idᵐ {A}) (idᵐ {B}) ≈ᵐ idᵐ
  mapˣᵐ-idᵐ =
    ≈ᵐ-sym (⟨⟩ᵐ-unique (idᵐ ∘ᵐ fstᵐ) (idᵐ ∘ᵐ sndᵐ) idᵐ
             (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
             (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))))

  -- pairing distributes over precomposition

  ⟨⟩ᵐ-∘ : ∀ {A B C D} → (f : B →ᵐ C) → (g : B →ᵐ D) → (h : A →ᵐ B)
        → ⟨ f , g ⟩ᵐ ∘ᵐ h ≈ᵐ ⟨ f ∘ᵐ h , g ∘ᵐ h ⟩ᵐ
  ⟨⟩ᵐ-∘ f g h =
    ⟨⟩ᵐ-unique (f ∘ᵐ h) (g ∘ᵐ h) (⟨ f , g ⟩ᵐ ∘ᵐ h)
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ ⟨ f , g ⟩ᵐ h)) (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ f g)))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ ⟨ f , g ⟩ᵐ h)) (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ f g)))

  -- the product functor's action distributes over a pairing

  mapˣᵐ-∘⟨⟩ : ∀ {A B C D E} → (a : B →ᵐ C) → (b : D →ᵐ E) → (u : A →ᵐ B) → (v : A →ᵐ D)
            → mapˣᵐ a b ∘ᵐ ⟨ u , v ⟩ᵐ ≈ᵐ ⟨ a ∘ᵐ u , b ∘ᵐ v ⟩ᵐ
  mapˣᵐ-∘⟨⟩ a b u v =
    ≈ᵐ-trans (⟨⟩ᵐ-∘ (a ∘ᵐ fstᵐ) (b ∘ᵐ sndᵐ) ⟨ u , v ⟩ᵐ)
      (⟨ ≈ᵐ-trans (∘ᵐ-assoc a fstᵐ ⟨ u , v ⟩ᵐ) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ u v))
       , ≈ᵐ-trans (∘ᵐ-assoc b sndᵐ ⟨ u , v ⟩ᵐ) (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ u v)) ⟩ᵐ-cong)

  -- congruence of the product functor's action

  mapˣᵐ-cong : ∀ {A B C D} {f f' : A →ᵐ C} {g g' : B →ᵐ D}
             → f ≈ᵐ f' → g ≈ᵐ g' → mapˣᵐ f g ≈ᵐ mapˣᵐ f' g'
  mapˣᵐ-cong p q = ⟨ ∘ᵐ-congˡ p , ∘ᵐ-congˡ q ⟩ᵐ-cong

  -- the product functor preserves composition

  mapˣᵐ-∘ : ∀ {A B C D E F} → (a : C →ᵐ E) → (b : D →ᵐ F)
          → (c : A →ᵐ C) → (d : B →ᵐ D)
          → mapˣᵐ a b ∘ᵐ mapˣᵐ c d ≈ᵐ mapˣᵐ (a ∘ᵐ c) (b ∘ᵐ d)
  mapˣᵐ-∘ a b c d =
    ≈ᵐ-trans (mapˣᵐ-∘⟨⟩ a b (c ∘ᵐ fstᵐ) (d ∘ᵐ sndᵐ))
             (⟨ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) , ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong)


  -- TRANSPORT ALONG EQUALITIES OF OBJECTS
  --
  -- The interpretation of a syntactic construct can land in a
  -- *propositionally* equal object (e.g. a context split rebuilt by
  -- `_++ᶜ_`), and the resulting `subst` then has to be pushed through `≈ᵐ`
  -- and through composition. Each is immediate once the equality is `refl`,
  -- which here is reached by applying `J` at an explicit motive (a record
  -- body may not case-split on `refl` itself).

  -- transport in a morphism's codomain

  substᶜ-≈ : ∀ {X A B} → (eq : A ≡ B) → {g g' : X →ᵐ A} → g ≈ᵐ g'
           → subst (λ O → X →ᵐ O) eq g ≈ᵐ subst (λ O → X →ᵐ O) eq g'
  substᶜ-≈ {X} eq {g} {g'} e =
    J (λ _ eq' → subst (λ O → X →ᵐ O) eq' g ≈ᵐ subst (λ O → X →ᵐ O) eq' g') eq e

  substᶜ-∘ : ∀ {X Y A B} → (eq : A ≡ B) → (g : X →ᵐ A) → (h : Y →ᵐ X)
           → subst (λ O → X →ᵐ O) eq g ∘ᵐ h ≡ subst (λ O → Y →ᵐ O) eq (g ∘ᵐ h)
  substᶜ-∘ {X} {Y} eq g h =
    J (λ _ eq' → subst (λ O → X →ᵐ O) eq' g ∘ᵐ h
               ≡ subst (λ O → Y →ᵐ O) eq' (g ∘ᵐ h)) eq refl

  -- transport in the second component of a morphism's product domain

  substᵈ-≈ : ∀ {X Z A B} → (eq : A ≡ B) → {g g' : (X ×ᵐ A) →ᵐ Z} → g ≈ᵐ g'
           → subst (λ O → (X ×ᵐ O) →ᵐ Z) eq g ≈ᵐ subst (λ O → (X ×ᵐ O) →ᵐ Z) eq g'
  substᵈ-≈ {X} {Z} eq {g} {g'} e =
    J (λ _ eq' → subst (λ O → (X ×ᵐ O) →ᵐ Z) eq' g
               ≈ᵐ subst (λ O → (X ×ᵐ O) →ᵐ Z) eq' g') eq e

  substᵈ-∘ : ∀ {W X Z A B} → (eq : A ≡ B) → (g : (X ×ᵐ A) →ᵐ Z) → (h : W →ᵐ X)
           → subst (λ O → (X ×ᵐ O) →ᵐ Z) eq g ∘ᵐ mapˣᵐ h idᵐ
           ≡ subst (λ O → (W ×ᵐ O) →ᵐ Z) eq (g ∘ᵐ mapˣᵐ h idᵐ)
  substᵈ-∘ {W} {X} {Z} eq g h =
    J (λ _ eq' → subst (λ O → (X ×ᵐ O) →ᵐ Z) eq' g ∘ᵐ mapˣᵐ h idᵐ
               ≡ subst (λ O → (W ×ᵐ O) →ᵐ Z) eq' (g ∘ᵐ mapˣᵐ h idᵐ)) eq refl

  -- associator of the product (and its inverse)

  ×ᵐ-assoc : ∀ {A B C} → (A ×ᵐ B) ×ᵐ C →ᵐ A ×ᵐ (B ×ᵐ C)
  ×ᵐ-assoc = ⟨ fstᵐ ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

  ×ᵐ-assoc⁻¹ : ∀ {A B C} → A ×ᵐ (B ×ᵐ C) →ᵐ (A ×ᵐ B) ×ᵐ C
  ×ᵐ-assoc⁻¹ = ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ

  -- the associator and its inverse are mutually inverse

  ×ᵐ-assoc-iso : ∀ {A B C} → ×ᵐ-assoc {A} {B} {C} ∘ᵐ ×ᵐ-assoc⁻¹ ≈ᵐ idᵐ
  ×ᵐ-assoc-iso = ≈ᵐ-trans
    (⟨⟩ᵐ-unique fstᵐ sndᵐ (×ᵐ-assoc ∘ᵐ ×ᵐ-assoc⁻¹)
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ ×ᵐ-assoc ×ᵐ-assoc⁻¹))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc fstᵐ fstᵐ ×ᵐ-assoc⁻¹)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _)))))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ ×ᵐ-assoc ×ᵐ-assoc⁻¹))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
      (≈ᵐ-trans (⟨⟩ᵐ-∘ (sndᵐ ∘ᵐ fstᵐ) sndᵐ ×ᵐ-assoc⁻¹)
      (≈ᵐ-trans (⟨ ≈ᵐ-trans (∘ᵐ-assoc sndᵐ fstᵐ ×ᵐ-assoc⁻¹)
                   (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _))
                , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                (≈ᵐ-sym (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ sndᵐ) (sndᵐ ∘ᵐ sndᵐ) sndᵐ ≈ᵐ-refl ≈ᵐ-refl)))))))
    (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ fstᵐ) (∘ᵐ-identityʳ sndᵐ)))

  ×ᵐ-assoc⁻¹-iso : ∀ {A B C} → ×ᵐ-assoc⁻¹ {A} {B} {C} ∘ᵐ ×ᵐ-assoc ≈ᵐ idᵐ
  ×ᵐ-assoc⁻¹-iso = ≈ᵐ-trans
    (⟨⟩ᵐ-unique fstᵐ sndᵐ (×ᵐ-assoc⁻¹ ∘ᵐ ×ᵐ-assoc)
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc fstᵐ ×ᵐ-assoc⁻¹ ×ᵐ-assoc))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))
      (≈ᵐ-trans (⟨⟩ᵐ-∘ fstᵐ (fstᵐ ∘ᵐ sndᵐ) ×ᵐ-assoc)
      (≈ᵐ-trans (⟨ ⟨⟩ᵐ-fstᵐ _ _
                , ≈ᵐ-trans (∘ᵐ-assoc fstᵐ sndᵐ ×ᵐ-assoc)
                   (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-fstᵐ _ _))
                ⟩ᵐ-cong)
                (≈ᵐ-sym (⟨⟩ᵐ-unique (fstᵐ ∘ᵐ fstᵐ) (sndᵐ ∘ᵐ fstᵐ) fstᵐ ≈ᵐ-refl ≈ᵐ-refl))))))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc sndᵐ ×ᵐ-assoc⁻¹ ×ᵐ-assoc))
      (≈ᵐ-trans (∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _))
      (≈ᵐ-trans (∘ᵐ-assoc sndᵐ sndᵐ ×ᵐ-assoc)
      (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)) (⟨⟩ᵐ-sndᵐ _ _))))))
    (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ fstᵐ) (∘ᵐ-identityʳ sndᵐ)))

  -- BOOLEAN OBJECT
  --
  -- Taken as primitive, with a three-argument eliminator `ifᵐ` rather than a
  -- copairing out of a coproduct, since `ifᵐ` is what the interpretation of
  -- `if_`then_`else_` applies directly. The block sits after the products
  -- because `ifᵐ-η` speaks about `⟨_,_⟩ᵐ`.
  --
  -- `ifᵐ-∘` is stability under precomposition, which is what the renaming and
  -- substitution coherence proofs consume; `ifᵐ-η` says a morphism out of
  -- `X ×ᵐ 𝔹ᵐ` is determined by its two instances, which is what makes the
  -- calculus's eta rule for `if` sound. Together the two say `𝔹ᵐ` is a
  -- *distributive* coproduct of two copies of `𝟙ᵐ`.

  field
    𝔹ᵐ : Obj

    trueᵐ  : 𝟙ᵐ →ᵐ 𝔹ᵐ
    falseᵐ : 𝟙ᵐ →ᵐ 𝔹ᵐ

    ifᵐ : ∀ {X A} → X →ᵐ 𝔹ᵐ → X →ᵐ A → X →ᵐ A → X →ᵐ A

    ifᵐ-cong : ∀ {X A} {b b' : X →ᵐ 𝔹ᵐ} {f f' g g' : X →ᵐ A}
             → b ≈ᵐ b' → f ≈ᵐ f' → g ≈ᵐ g'
             → ifᵐ b f g ≈ᵐ ifᵐ b' f' g'

    ifᵐ-true  : ∀ {X A} → (f g : X →ᵐ A)
              → ifᵐ (trueᵐ ∘ᵐ terminalᵐ) f g ≈ᵐ f
    ifᵐ-false : ∀ {X A} → (f g : X →ᵐ A)
              → ifᵐ (falseᵐ ∘ᵐ terminalᵐ) f g ≈ᵐ g

    ifᵐ-∘ : ∀ {X Y A} → (b : X →ᵐ 𝔹ᵐ) → (f g : X →ᵐ A) → (h : Y →ᵐ X)
          → ifᵐ b f g ∘ᵐ h ≈ᵐ ifᵐ (b ∘ᵐ h) (f ∘ᵐ h) (g ∘ᵐ h)

    ifᵐ-η : ∀ {X A} → (b : X →ᵐ 𝔹ᵐ) → (m : X ×ᵐ 𝔹ᵐ →ᵐ A)
          → m ∘ᵐ ⟨ idᵐ , b ⟩ᵐ
          ≈ᵐ ifᵐ b (m ∘ᵐ ⟨ idᵐ , trueᵐ  ∘ᵐ terminalᵐ ⟩ᵐ)
                   (m ∘ᵐ ⟨ idᵐ , falseᵐ ∘ᵐ terminalᵐ ⟩ᵐ)

  -- EXPONENTIALS

  field
    _⇒ᵐ_ : Obj → Obj → Obj

    curryᵐ : ∀ {A B C} → A ×ᵐ B →ᵐ C → A →ᵐ B ⇒ᵐ C
    curryᵐ-cong : ∀ {A B C} {f g : A ×ᵐ B →ᵐ C} → f ≈ᵐ g → curryᵐ f ≈ᵐ curryᵐ g
    curryᵐ-nat : ∀ {A B C D} → (f : A →ᵐ B) → (g : B ×ᵐ C →ᵐ D)
               → curryᵐ (g ∘ᵐ mapˣᵐ f idᵐ) ≈ᵐ curryᵐ g ∘ᵐ f

    uncurryᵐ : ∀ {A B C} → A →ᵐ B ⇒ᵐ C → A ×ᵐ B →ᵐ C
    uncurryᵐ-cong : ∀ {A B C} {f g : A →ᵐ B ⇒ᵐ C} → f ≈ᵐ g → uncurryᵐ f ≈ᵐ uncurryᵐ g
    uncurryᵐ-nat : ∀ {A B C D} → (f : A →ᵐ B) → (g : B →ᵐ C ⇒ᵐ D)
                 → uncurryᵐ (g ∘ᵐ f) ≈ᵐ uncurryᵐ g ∘ᵐ mapˣᵐ f idᵐ

    curryᵐ-uncurryᵐ-iso : ∀ {A B C} → (f : A ×ᵐ B →ᵐ C)
                        → uncurryᵐ (curryᵐ f) ≈ᵐ f
    uncurryᵐ-curryᵐ-iso : ∀ {A B C} → (f : A →ᵐ B ⇒ᵐ C)
                        → curryᵐ (uncurryᵐ f) ≈ᵐ f

    -- The exponential's costrength `A ×ᵐ (B ⇒ᵐ C) →ᵐ B ⇒ᵐ (A ×ᵐ C)`, taken
    -- as primitive (it is definable as `curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ
    -- sndᵐ ⟩ᵐ`, but an instance may supply a computationally lighter one).
    -- `exp-strᵐ-def` pins it to that definition.

    exp-strᵐ : ∀ {A B C} → A ×ᵐ (B ⇒ᵐ C) →ᵐ B ⇒ᵐ (A ×ᵐ C)
    exp-strᵐ-def : ∀ {A B C}
                 → exp-strᵐ {A} {B} {C} ≈ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ

  infixr 22 _⇒ᵐ_

  -- evaluation and the functorial action of the exponential

  appᵐ : ∀ {A B} → (A ⇒ᵐ B) ×ᵐ A →ᵐ B
  appᵐ = uncurryᵐ idᵐ

  map⇒ᵐ : ∀ {A B C D} → A →ᵐ B → C →ᵐ D → B ⇒ᵐ C →ᵐ A ⇒ᵐ D
  map⇒ᵐ f g = curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)

  -- beta: applying an abstraction is substituting into its body

  βᵐ : ∀ {A B C} → (f : A ×ᵐ B →ᵐ C) → (g : A →ᵐ B)
     → appᵐ ∘ᵐ ⟨ curryᵐ f , g ⟩ᵐ ≈ᵐ f ∘ᵐ ⟨ idᵐ , g ⟩ᵐ
  βᵐ f g =
    ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘⟨⟩ (curryᵐ f) idᵐ idᵐ g)
                                        (⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (uncurryᵐ-nat (curryᵐ f) idᵐ)))
              (∘ᵐ-congˡ (≈ᵐ-trans (uncurryᵐ-cong (∘ᵐ-identityˡ _))
                                  (curryᵐ-uncurryᵐ-iso f)))))

  -- Postcomposing an abstraction's body: the functorial action of the
  -- exponential on the codomain absorbs into the abstraction.

  map⇒ᵐ-curryᵐ : ∀ {A B C D} → (h : C →ᵐ D) → (k : A ×ᵐ B →ᵐ C)
               → map⇒ᵐ idᵐ h ∘ᵐ curryᵐ k ≈ᵐ curryᵐ (h ∘ᵐ k)
  map⇒ᵐ-curryᵐ h k =
    ≈ᵐ-trans (≈ᵐ-sym (curryᵐ-nat (curryᵐ k) (h ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ idᵐ)))
      (curryᵐ-cong
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (∘ᵐ-congʳ
            (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-congʳ mapˣᵐ-idᵐ))
            (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityʳ _))
            (≈ᵐ-trans (≈ᵐ-sym (uncurryᵐ-nat (curryᵐ k) idᵐ))
                      (≈ᵐ-trans (uncurryᵐ-cong (∘ᵐ-identityˡ _))
                                (curryᵐ-uncurryᵐ-iso k))))))))

  -- the exponential functor preserves identities

  map⇒ᵐ-idᵐ : ∀ {A B} → map⇒ᵐ (idᵐ {A}) (idᵐ {B}) ≈ᵐ idᵐ
  map⇒ᵐ-idᵐ =
    ≈ᵐ-trans (curryᵐ-cong
               (≈ᵐ-trans (∘ᵐ-identityˡ _)
                         (≈ᵐ-trans (∘ᵐ-congʳ mapˣᵐ-idᵐ) (∘ᵐ-identityʳ _))))
             (uncurryᵐ-curryᵐ-iso idᵐ)

  -- Precomposing an abstraction's *argument*: the functorial action of the
  -- exponential on the domain reindexes what the abstraction is applied to.

  map⇒ᵐ-curryᵐˡ : ∀ {A B C D} → (f : A →ᵐ B) → (k : C ×ᵐ B →ᵐ D)
                → map⇒ᵐ f idᵐ ∘ᵐ curryᵐ k ≈ᵐ curryᵐ (k ∘ᵐ mapˣᵐ idᵐ f)
  map⇒ᵐ-curryᵐˡ f k =
    ≈ᵐ-trans (≈ᵐ-sym (curryᵐ-nat (curryᵐ k) (idᵐ ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)))
      (curryᵐ-cong
        (≈ᵐ-trans (∘ᵐ-congˡ (∘ᵐ-identityˡ _))
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        -- the two product maps compose, and split off the argument's reindexing
        (≈ᵐ-trans (∘ᵐ-congʳ
                    (≈ᵐ-trans (mapˣᵐ-∘ idᵐ f (curryᵐ k) idᵐ)
                    (≈ᵐ-trans (mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _))
                              (≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘ (curryᵐ k) idᵐ idᵐ f)
                                                (mapˣᵐ-cong (∘ᵐ-identityʳ _)
                                                            (∘ᵐ-identityˡ _)))))))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                  -- what is left of the application is the abstraction undone
                  (∘ᵐ-congˡ
                    (≈ᵐ-trans (≈ᵐ-sym (uncurryᵐ-nat (curryᵐ k) idᵐ))
                    (≈ᵐ-trans (uncurryᵐ-cong (∘ᵐ-identityˡ _))
                              (curryᵐ-uncurryᵐ-iso k)))))))))

  -- The exponential's costrength applied to a pair whose second component is
  -- an abstraction: the paired-in value simply joins the abstraction's
  -- environment (it is constant in the abstracted argument, hence `fstᵐ`).

  exp-strᵐ-⟨⟩ : ∀ {A B C D} → (f : A →ᵐ B) → (g : A ×ᵐ C →ᵐ D)
              → exp-strᵐ ∘ᵐ ⟨ f , curryᵐ g ⟩ᵐ ≈ᵐ curryᵐ ⟨ f ∘ᵐ fstᵐ , g ⟩ᵐ
  exp-strᵐ-⟨⟩ f g =
    ≈ᵐ-trans (∘ᵐ-congˡ exp-strᵐ-def)
    (≈ᵐ-trans (≈ᵐ-sym (curryᵐ-nat ⟨ f , curryᵐ g ⟩ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ))
      (curryᵐ-cong
        (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
          (⟨ -- the value: projected out of the pair, constant in the argument
             ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
             (≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
             (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                       (∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _))))
             -- the body: the abstraction is undone by the application
           , ≈ᵐ-trans (≈ᵐ-sym (uncurryᵐ-nat ⟨ f , curryᵐ g ⟩ᵐ sndᵐ))
             (≈ᵐ-trans (uncurryᵐ-cong (⟨⟩ᵐ-sndᵐ _ _))
                       (curryᵐ-uncurryᵐ-iso g)) ⟩ᵐ-cong))))
