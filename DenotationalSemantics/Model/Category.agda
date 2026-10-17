------------------------------------------------------------------------
-- Setoid-enriched cartesian closed category structure for the models --
-- of the language.                                                   --
--                                                                    --
-- Each hom-set carries an equivalence relation `_≈ᵐ_` of morphism    --
-- equality, and every equational law is stated up to `_≈ᵐ_`, so that --
-- the context (possibility) modality may be realised as a coend.     --
--                                                                    --
-- Beyond the core (identities, composition, and its congruence) the  --
-- record carries the cartesian closed structure and binary           --
-- coproducts, with the congruences needed to reason up to `_≈ᵐ_`.    --
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

    -- The initial object is strict: an object admitting a map to `𝟘ᵐ` is itself
    -- initial, so any two maps out of it agree.

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
  -- The interpretation of a syntactic construct can land in a propositionally
  -- equal object, and the resulting `subst` then has to be pushed through `≈ᵐ`
  -- and through composition. Each is proved by applying `J` at an explicit
  -- motive, a record body not being allowed to case-split on `refl`.

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
  -- copairing out of a coproduct. The block sits after the products because
  -- `ifᵐ-η` speaks about `⟨_,_⟩ᵐ`.
  --
  -- `ifᵐ-∘` is stability under precomposition; `ifᵐ-η` says a morphism out of
  -- `X ×ᵐ 𝔹ᵐ` is determined by its two instances.

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

  -- BINARY COPRODUCTS
  --
  -- Plain coproducts: copairing with its two β laws and uniqueness. The
  -- eliminator stable under a context, `caseᵐ`, is derived below from the
  -- exponentials.

  field
    _+ᵐ_ : Obj → Obj → Obj

    inlᵐ : ∀ {A B} → A →ᵐ A +ᵐ B
    inrᵐ : ∀ {A B} → B →ᵐ A +ᵐ B
    [_,_]ᵐ : ∀ {A B C} → A →ᵐ C → B →ᵐ C → A +ᵐ B →ᵐ C

    [_,_]ᵐ-cong : ∀ {A B C} {f f' : A →ᵐ C} {g g' : B →ᵐ C}
                → f ≈ᵐ f' → g ≈ᵐ g' → [ f , g ]ᵐ ≈ᵐ [ f' , g' ]ᵐ

    []ᵐ-inlᵐ : ∀ {A B C} → (f : A →ᵐ C) → (g : B →ᵐ C) → [ f , g ]ᵐ ∘ᵐ inlᵐ ≈ᵐ f
    []ᵐ-inrᵐ : ∀ {A B C} → (f : A →ᵐ C) → (g : B →ᵐ C) → [ f , g ]ᵐ ∘ᵐ inrᵐ ≈ᵐ g
    []ᵐ-unique : ∀ {A B C} → (f : A →ᵐ C) → (g : B →ᵐ C) → (h : A +ᵐ B →ᵐ C)
               → h ∘ᵐ inlᵐ ≈ᵐ f → h ∘ᵐ inrᵐ ≈ᵐ g → h ≈ᵐ [ f , g ]ᵐ

  infixr 22 _+ᵐ_

  -- copairing absorbs a postcomposition

  []ᵐ-post : ∀ {A B C D} → (f : A →ᵐ C) → (g : B →ᵐ C) → (h : C →ᵐ D)
           → h ∘ᵐ [ f , g ]ᵐ ≈ᵐ [ h ∘ᵐ f , h ∘ᵐ g ]ᵐ
  []ᵐ-post f g h =
    []ᵐ-unique _ _ _
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ ([]ᵐ-inlᵐ f g)))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ ([]ᵐ-inrᵐ f g)))

  -- functorial action of the coproduct

  map+ᵐ : ∀ {A B C D} → A →ᵐ C → B →ᵐ D → A +ᵐ B →ᵐ C +ᵐ D
  map+ᵐ f g = [ inlᵐ ∘ᵐ f , inrᵐ ∘ᵐ g ]ᵐ

  map+ᵐ-cong : ∀ {A B C D} {f f' : A →ᵐ C} {g g' : B →ᵐ D}
             → f ≈ᵐ f' → g ≈ᵐ g' → map+ᵐ f g ≈ᵐ map+ᵐ f' g'
  map+ᵐ-cong p q = [ ∘ᵐ-congʳ p , ∘ᵐ-congʳ q ]ᵐ-cong

  map+ᵐ-idᵐ : ∀ {A B} → map+ᵐ (idᵐ {A}) (idᵐ {B}) ≈ᵐ idᵐ
  map+ᵐ-idᵐ =
    ≈ᵐ-sym ([]ᵐ-unique _ _ idᵐ
             (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _)))
             (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _))))

  -- a copairing precomposed with the coproduct's action

  []ᵐ-map+ᵐ : ∀ {A B C D E} → (f : C →ᵐ E) → (g : D →ᵐ E)
            → (a : A →ᵐ C) → (b : B →ᵐ D)
            → [ f , g ]ᵐ ∘ᵐ map+ᵐ a b ≈ᵐ [ f ∘ᵐ a , g ∘ᵐ b ]ᵐ
  []ᵐ-map+ᵐ f g a b =
    []ᵐ-unique _ _ _
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ ([]ᵐ-inlᵐ _ _))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ([]ᵐ-inlᵐ f g)))))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ ([]ᵐ-inrᵐ _ _))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ ([]ᵐ-inrᵐ f g)))))

  map+ᵐ-∘ : ∀ {A B C D E F} → (a : C →ᵐ E) → (b : D →ᵐ F)
          → (c : A →ᵐ C) → (d : B →ᵐ D)
          → map+ᵐ a b ∘ᵐ map+ᵐ c d ≈ᵐ map+ᵐ (a ∘ᵐ c) (b ∘ᵐ d)
  map+ᵐ-∘ a b c d =
    ≈ᵐ-trans ([]ᵐ-map+ᵐ _ _ c d)
             [ ∘ᵐ-assoc _ _ _ , ∘ᵐ-assoc _ _ _ ]ᵐ-cong

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

    -- The exponential's costrength, taken as primitive so that an instance may
    -- supply a computationally lighter one; `exp-strᵐ-def` pins it to the
    -- definable morphism.

    exp-strᵐ : ∀ {A B C} → A ×ᵐ (B ⇒ᵐ C) →ᵐ B ⇒ᵐ (A ×ᵐ C)
    exp-strᵐ-def : ∀ {A B C}
                 → exp-strᵐ {A} {B} {C} ≈ᵐ curryᵐ ⟨ fstᵐ ∘ᵐ fstᵐ , uncurryᵐ sndᵐ ⟩ᵐ

  infixr 22 _⇒ᵐ_

  -- evaluation and the functorial action of the exponential

  appᵐ : ∀ {A B} → (A ⇒ᵐ B) ×ᵐ A →ᵐ B
  appᵐ = uncurryᵐ idᵐ

  map⇒ᵐ : ∀ {A B C D} → A →ᵐ B → C →ᵐ D → B ⇒ᵐ C →ᵐ A ⇒ᵐ D
  map⇒ᵐ f g = curryᵐ (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)

  map⇒ᵐ-cong : ∀ {A B C D} {f f' : A →ᵐ B} {g g' : C →ᵐ D}
             → f ≈ᵐ f' → g ≈ᵐ g' → map⇒ᵐ f g ≈ᵐ map⇒ᵐ f' g'
  map⇒ᵐ-cong p q = curryᵐ-cong (∘ᵐ-cong q (∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl p)))

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

  -- applying an abstraction undoes it

  appᵐ-curryᵐ : ∀ {X A B} → (k : X ×ᵐ A →ᵐ B)
              → appᵐ ∘ᵐ mapˣᵐ (curryᵐ k) idᵐ ≈ᵐ k
  appᵐ-curryᵐ k =
    ≈ᵐ-trans (≈ᵐ-sym (uncurryᵐ-nat (curryᵐ k) idᵐ))
    (≈ᵐ-trans (uncurryᵐ-cong (∘ᵐ-identityˡ _))
              (curryᵐ-uncurryᵐ-iso k))

  -- application reindexed by the exponential's functorial action

  appᵐ-map⇒ᵐ : ∀ {X A B C D} → (f : A →ᵐ B) → (g : C →ᵐ D) → (b : X →ᵐ A)
             → appᵐ ∘ᵐ mapˣᵐ (map⇒ᵐ f g) b
             ≈ᵐ g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ (f ∘ᵐ b)
  appᵐ-map⇒ᵐ f g b =
    ≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘ (map⇒ᵐ f g) idᵐ idᵐ b)
                                        (mapˣᵐ-cong (∘ᵐ-identityʳ _)
                                                    (∘ᵐ-identityˡ _)))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (appᵐ-curryᵐ _))
    (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-trans (mapˣᵐ-∘ idᵐ f idᵐ b)
                                           (mapˣᵐ-cong (∘ᵐ-identityˡ _)
                                                       ≈ᵐ-refl))))))))

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

  -- Both reindexings of an abstraction at once; `map⇒ᵐ-curryᵐ` and
  -- `map⇒ᵐ-curryᵐˡ` are the cases `f ≔ idᵐ` and `g ≔ idᵐ`.

  map⇒ᵐ-curryᵐˡʳ : ∀ {A A' B C D} → (f : A' →ᵐ A) → (g : C →ᵐ D) → (k : B ×ᵐ A →ᵐ C)
                 → map⇒ᵐ f g ∘ᵐ curryᵐ k ≈ᵐ curryᵐ (g ∘ᵐ k ∘ᵐ mapˣᵐ idᵐ f)
  map⇒ᵐ-curryᵐˡʳ f g k =
    ≈ᵐ-trans (≈ᵐ-sym (curryᵐ-nat (curryᵐ k) (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f)))
      (curryᵐ-cong
        (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (∘ᵐ-congʳ
            (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
            -- the two product maps commute, splitting off the argument's reindexing
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
                                  (curryᵐ-uncurryᵐ-iso k))))))))))

  -- the exponential is a bifunctor, contravariant in the domain

  map⇒ᵐ-∘ : ∀ {A A' B C D D'} → (f : A →ᵐ B) → (f' : A' →ᵐ A)
          → (g : C →ᵐ D) → (g' : D →ᵐ D')
          → map⇒ᵐ (f ∘ᵐ f') (g' ∘ᵐ g) ≈ᵐ map⇒ᵐ f' g' ∘ᵐ map⇒ᵐ f g
  map⇒ᵐ-∘ f f' g g' =
    ≈ᵐ-sym
      (≈ᵐ-trans (map⇒ᵐ-curryᵐˡʳ f' g' (g ∘ᵐ appᵐ ∘ᵐ mapˣᵐ idᵐ f))
        (curryᵐ-cong
          (≈ᵐ-trans (∘ᵐ-congʳ
                      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                        (∘ᵐ-congʳ
                          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
                                    (∘ᵐ-congʳ
                                      (≈ᵐ-trans (mapˣᵐ-∘ idᵐ f idᵐ f')
                                                (mapˣᵐ-cong (∘ᵐ-identityˡ _) ≈ᵐ-refl)))))))
                    (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

  -- the exponential's action on the codomain alone is functorial

  map⇒ᵐ-∘ʳ : ∀ {A B C D} → (g : C →ᵐ D) → (h : B →ᵐ C)
           → map⇒ᵐ (idᵐ {A}) (g ∘ᵐ h) ≈ᵐ map⇒ᵐ idᵐ g ∘ᵐ map⇒ᵐ idᵐ h
  map⇒ᵐ-∘ʳ g h =
    ≈ᵐ-sym (≈ᵐ-trans (map⇒ᵐ-curryᵐ g _)
                     (curryᵐ-cong (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))

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

  -- postcomposing a boolean elimination (only precomposition is a field)

  ifᵐ-post : ∀ {X A B} → (b : X →ᵐ 𝔹ᵐ) → (m n : X →ᵐ A) → (g : A →ᵐ B)
           → g ∘ᵐ ifᵐ b m n ≈ᵐ ifᵐ b (g ∘ᵐ m) (g ∘ᵐ n)
  ifᵐ-post {X} {A} b m n g =
    ≈ᵐ-trans (≈ᵐ-sym lhs)
    (≈ᵐ-trans (ifᵐ-η b (g ∘ᵐ ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ)))
              (ifᵐ-cong ≈ᵐ-refl
                        (≈ᵐ-trans branch (∘ᵐ-congʳ (ifᵐ-true m n)))
                        (≈ᵐ-trans branch (∘ᵐ-congʳ (ifᵐ-false m n)))))
    where
      step : ∀ {Y} → (u : Y →ᵐ X) → (c : Y →ᵐ 𝔹ᵐ)
           → ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ) ∘ᵐ ⟨ u , c ⟩ᵐ ≈ᵐ ifᵐ c (m ∘ᵐ u) (n ∘ᵐ u)
      step u c =
        ≈ᵐ-trans (ifᵐ-∘ _ _ _ _)
                 (ifᵐ-cong (⟨⟩ᵐ-sndᵐ _ _)
                           (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)))
                           (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))))

      lhs : (g ∘ᵐ ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ)) ∘ᵐ ⟨ idᵐ , b ⟩ᵐ
          ≈ᵐ g ∘ᵐ ifᵐ b m n
      lhs =
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (step idᵐ b))
                  (∘ᵐ-congʳ (ifᵐ-cong ≈ᵐ-refl (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))))

      branch : ∀ {c : 𝟙ᵐ →ᵐ 𝔹ᵐ}
             → (g ∘ᵐ ifᵐ sndᵐ (m ∘ᵐ fstᵐ) (n ∘ᵐ fstᵐ))
                 ∘ᵐ ⟨ idᵐ , c ∘ᵐ terminalᵐ ⟩ᵐ
             ≈ᵐ g ∘ᵐ ifᵐ (c ∘ᵐ terminalᵐ) m n
      branch =
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (step idᵐ _))
                  (∘ᵐ-congʳ (ifᵐ-cong ≈ᵐ-refl (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _))))


  -- SUMS IN A CONTEXT
  --
  -- `X ×ᵐ -` preserves the coproduct, being left adjoint to `X ⇒ᵐ -`: a map
  -- out of `X ×ᵐ (A +ᵐ B)` is the copairing `copairˣᵐ` of its two
  -- restrictions. `caseᵐ` is the eliminator this yields, with the laws that
  -- `ifᵐ` has as fields.

  swapᵐ : ∀ {A B} → A ×ᵐ B →ᵐ B ×ᵐ A
  swapᵐ = ⟨ sndᵐ , fstᵐ ⟩ᵐ

  swapᵐ-⟨⟩ : ∀ {X A B} → (f : X →ᵐ A) → (g : X →ᵐ B)
           → swapᵐ ∘ᵐ ⟨ f , g ⟩ᵐ ≈ᵐ ⟨ g , f ⟩ᵐ
  swapᵐ-⟨⟩ f g = ≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _) ⟨ ⟨⟩ᵐ-sndᵐ f g , ⟨⟩ᵐ-fstᵐ f g ⟩ᵐ-cong

  swapᵐ-swapᵐ : ∀ {A B} → swapᵐ {B} {A} ∘ᵐ swapᵐ {A} {B} ≈ᵐ idᵐ
  swapᵐ-swapᵐ =
    ≈ᵐ-trans (swapᵐ-⟨⟩ sndᵐ fstᵐ)
             (≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))

  swapᵐ-mapˣᵐ : ∀ {A B C D} → (a : A →ᵐ C) → (b : B →ᵐ D)
              → swapᵐ ∘ᵐ mapˣᵐ a b ≈ᵐ mapˣᵐ b a ∘ᵐ swapᵐ
  swapᵐ-mapˣᵐ a b =
    ≈ᵐ-trans (swapᵐ-⟨⟩ _ _) (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ b a sndᵐ fstᵐ))

  -- the two factors of a product act independently

  mapˣᵐ-comm : ∀ {A B C D} → (a : A →ᵐ C) → (b : B →ᵐ D)
             → mapˣᵐ a idᵐ ∘ᵐ mapˣᵐ idᵐ b ≈ᵐ mapˣᵐ idᵐ b ∘ᵐ mapˣᵐ a idᵐ
  mapˣᵐ-comm a b =
    ≈ᵐ-trans (mapˣᵐ-∘ a idᵐ idᵐ b)
    (≈ᵐ-trans (mapˣᵐ-cong (≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _)))
                          (≈ᵐ-trans (∘ᵐ-identityˡ _) (≈ᵐ-sym (∘ᵐ-identityʳ _))))
              (≈ᵐ-sym (mapˣᵐ-∘ idᵐ b a idᵐ)))

  -- a pairing with an injected second component

  ⟨⟩ᵐ-mapˣᵐ : ∀ {X A B} → (ι : A →ᵐ B) → (a : X →ᵐ A)
            → ⟨ idᵐ , ι ∘ᵐ a ⟩ᵐ ≈ᵐ mapˣᵐ idᵐ ι ∘ᵐ ⟨ idᵐ , a ⟩ᵐ
  ⟨⟩ᵐ-mapˣᵐ ι a =
    ≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘⟨⟩ idᵐ ι idᵐ a) ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)

  copairˣᵐ : ∀ {X A B C} → X ×ᵐ A →ᵐ C → X ×ᵐ B →ᵐ C → X ×ᵐ (A +ᵐ B) →ᵐ C
  copairˣᵐ f g =
    uncurryᵐ [ curryᵐ (f ∘ᵐ swapᵐ) , curryᵐ (g ∘ᵐ swapᵐ) ]ᵐ ∘ᵐ swapᵐ

  copairˣᵐ-cong : ∀ {X A B C} {f f' : X ×ᵐ A →ᵐ C} {g g' : X ×ᵐ B →ᵐ C}
                → f ≈ᵐ f' → g ≈ᵐ g' → copairˣᵐ f g ≈ᵐ copairˣᵐ f' g'
  copairˣᵐ-cong p q =
    ∘ᵐ-congˡ (uncurryᵐ-cong [ curryᵐ-cong (∘ᵐ-congˡ p)
                            , curryᵐ-cong (∘ᵐ-congˡ q) ]ᵐ-cong)

  -- β: the restriction of the transposed copairing along an injection

  private
    copairˣᵐ-β : ∀ {X A A' C} → (k : A →ᵐ X ⇒ᵐ C) → (ι : A' →ᵐ A)
               → (f : X ×ᵐ A' →ᵐ C) → k ∘ᵐ ι ≈ᵐ curryᵐ (f ∘ᵐ swapᵐ)
               → (uncurryᵐ k ∘ᵐ swapᵐ) ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ f
    copairˣᵐ-β k ι f p =
      ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ (swapᵐ-mapˣᵐ idᵐ ι))
      (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (uncurryᵐ-nat ι k)))
      (≈ᵐ-trans (∘ᵐ-congˡ (uncurryᵐ-cong p))
      (≈ᵐ-trans (∘ᵐ-congˡ (curryᵐ-uncurryᵐ-iso _))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
      (≈ᵐ-trans (∘ᵐ-congʳ swapᵐ-swapᵐ) (∘ᵐ-identityʳ f))))))))

    -- the transpose of a map restricted along an injection
    copairˣᵐ-restrict : ∀ {X A A' C} → (h : X ×ᵐ A →ᵐ C) → (ι : A' →ᵐ A)
                      → (f : X ×ᵐ A' →ᵐ C) → h ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ f
                      → curryᵐ (h ∘ᵐ swapᵐ) ∘ᵐ ι ≈ᵐ curryᵐ (f ∘ᵐ swapᵐ)
    copairˣᵐ-restrict h ι f p =
      ≈ᵐ-trans (≈ᵐ-sym (curryᵐ-nat ι (h ∘ᵐ swapᵐ)))
        (curryᵐ-cong
          (≈ᵐ-trans (∘ᵐ-assoc _ _ _)
          (≈ᵐ-trans (∘ᵐ-congʳ (swapᵐ-mapˣᵐ ι idᵐ))
          (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ p)))))

  copairˣᵐ-inl : ∀ {X A B C} → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
               → copairˣᵐ f g ∘ᵐ mapˣᵐ idᵐ inlᵐ ≈ᵐ f
  copairˣᵐ-inl f g = copairˣᵐ-β _ inlᵐ f ([]ᵐ-inlᵐ _ _)

  copairˣᵐ-inr : ∀ {X A B C} → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
               → copairˣᵐ f g ∘ᵐ mapˣᵐ idᵐ inrᵐ ≈ᵐ g
  copairˣᵐ-inr f g = copairˣᵐ-β _ inrᵐ g ([]ᵐ-inrᵐ _ _)

  copairˣᵐ-unique : ∀ {X A B C} → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
                  → (h : X ×ᵐ (A +ᵐ B) →ᵐ C)
                  → h ∘ᵐ mapˣᵐ idᵐ inlᵐ ≈ᵐ f → h ∘ᵐ mapˣᵐ idᵐ inrᵐ ≈ᵐ g
                  → h ≈ᵐ copairˣᵐ f g
  copairˣᵐ-unique f g h p q =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ h))
    (≈ᵐ-trans (∘ᵐ-congʳ (≈ᵐ-sym swapᵐ-swapᵐ))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
    (≈ᵐ-trans (∘ᵐ-congˡ (≈ᵐ-sym (curryᵐ-uncurryᵐ-iso (h ∘ᵐ swapᵐ))))
              (∘ᵐ-congˡ (uncurryᵐ-cong
                ([]ᵐ-unique _ _ _ (copairˣᵐ-restrict h inlᵐ f p)
                                  (copairˣᵐ-restrict h inrᵐ g q)))))))

  -- reindexing the context

  copairˣᵐ-∘ : ∀ {Y X A B C} → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
             → (h : Y →ᵐ X)
             → copairˣᵐ f g ∘ᵐ mapˣᵐ h idᵐ
             ≈ᵐ copairˣᵐ (f ∘ᵐ mapˣᵐ h idᵐ) (g ∘ᵐ mapˣᵐ h idᵐ)
  copairˣᵐ-∘ {Y} {X} {A} {B} {C} f g h = copairˣᵐ-unique _ _ _ (side inlᵐ (copairˣᵐ-inl f g))
                                           (side inrᵐ (copairˣᵐ-inr f g))
    where
      side : ∀ {A'} {k : X ×ᵐ A' →ᵐ C} → (ι : A' →ᵐ A +ᵐ B)
           → copairˣᵐ f g ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ k
           → (copairˣᵐ f g ∘ᵐ mapˣᵐ h idᵐ) ∘ᵐ mapˣᵐ idᵐ ι ≈ᵐ k ∘ᵐ mapˣᵐ h idᵐ
      side ι p =
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ (mapˣᵐ-comm h ι))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ p)))

  -- reindexing the summands

  copairˣᵐ-map+ᵐ : ∀ {X A A' B B' C} → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
                 → (a : A' →ᵐ A) → (b : B' →ᵐ B)
                 → copairˣᵐ f g ∘ᵐ mapˣᵐ idᵐ (map+ᵐ a b)
                 ≈ᵐ copairˣᵐ (f ∘ᵐ mapˣᵐ idᵐ a) (g ∘ᵐ mapˣᵐ idᵐ b)
  copairˣᵐ-map+ᵐ {X} {A} {A'} {B} {B'} {C} f g a b =
    copairˣᵐ-unique _ _ _ (side inlᵐ inlᵐ a ([]ᵐ-inlᵐ _ _) (copairˣᵐ-inl f g))
                          (side inrᵐ inrᵐ b ([]ᵐ-inrᵐ _ _) (copairˣᵐ-inr f g))
    where
      side : ∀ {A₀ A₁} {k : X ×ᵐ A₁ →ᵐ C}
           → (ι : A₀ →ᵐ _) → (ι' : A₁ →ᵐ A +ᵐ B) → (c : A₀ →ᵐ A₁)
           → map+ᵐ a b ∘ᵐ ι ≈ᵐ ι' ∘ᵐ c
           → copairˣᵐ f g ∘ᵐ mapˣᵐ idᵐ ι' ≈ᵐ k
           → (copairˣᵐ f g ∘ᵐ mapˣᵐ idᵐ (map+ᵐ a b)) ∘ᵐ mapˣᵐ idᵐ ι
             ≈ᵐ k ∘ᵐ mapˣᵐ idᵐ c
      side ι ι' c e p =
        ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
        (≈ᵐ-trans (∘ᵐ-congʳ
          (≈ᵐ-trans (mapˣᵐ-∘ idᵐ (map+ᵐ a b) idᵐ ι)
          (≈ᵐ-trans (mapˣᵐ-cong ≈ᵐ-refl e)
                    (≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘ idᵐ ι' idᵐ c)
                                      (mapˣᵐ-cong ≈ᵐ-refl ≈ᵐ-refl))))))
        (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ p)))

  -- absorbing a postcomposition

  copairˣᵐ-post : ∀ {X A B C D} → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
                → (k : C →ᵐ D)
                → k ∘ᵐ copairˣᵐ f g ≈ᵐ copairˣᵐ (k ∘ᵐ f) (k ∘ᵐ g)
  copairˣᵐ-post f g k =
    copairˣᵐ-unique _ _ _
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (copairˣᵐ-inl f g)))
      (≈ᵐ-trans (∘ᵐ-assoc _ _ _) (∘ᵐ-congʳ (copairˣᵐ-inr f g)))

  -- The eliminator: a scrutinee and two branches over the context.

  caseᵐ : ∀ {X A B C} → X →ᵐ A +ᵐ B → X ×ᵐ A →ᵐ C → X ×ᵐ B →ᵐ C → X →ᵐ C
  caseᵐ s f g = copairˣᵐ f g ∘ᵐ ⟨ idᵐ , s ⟩ᵐ

  caseᵐ-cong : ∀ {X A B C} {s s' : X →ᵐ A +ᵐ B}
               {f f' : X ×ᵐ A →ᵐ C} {g g' : X ×ᵐ B →ᵐ C}
             → s ≈ᵐ s' → f ≈ᵐ f' → g ≈ᵐ g' → caseᵐ s f g ≈ᵐ caseᵐ s' f' g'
  caseᵐ-cong ps pf pg = ∘ᵐ-cong (copairˣᵐ-cong pf pg) ⟨ ≈ᵐ-refl , ps ⟩ᵐ-cong

  caseᵐ-inl : ∀ {X A B C} → (a : X →ᵐ A)
            → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
            → caseᵐ (inlᵐ ∘ᵐ a) f g ≈ᵐ f ∘ᵐ ⟨ idᵐ , a ⟩ᵐ
  caseᵐ-inl a f g =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-mapˣᵐ inlᵐ a))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (copairˣᵐ-inl f g)))

  caseᵐ-inr : ∀ {X A B C} → (b : X →ᵐ B)
            → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
            → caseᵐ (inrᵐ ∘ᵐ b) f g ≈ᵐ g ∘ᵐ ⟨ idᵐ , b ⟩ᵐ
  caseᵐ-inr b f g =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-mapˣᵐ inrᵐ b))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (copairˣᵐ-inr f g)))

  caseᵐ-∘ : ∀ {Y X A B C} → (s : X →ᵐ A +ᵐ B)
          → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C) → (h : Y →ᵐ X)
          → caseᵐ s f g ∘ᵐ h
          ≈ᵐ caseᵐ (s ∘ᵐ h) (f ∘ᵐ mapˣᵐ h idᵐ) (g ∘ᵐ mapˣᵐ h idᵐ)
  caseᵐ-∘ s f g h =
    ≈ᵐ-trans (∘ᵐ-assoc _ _ _)
    (≈ᵐ-trans (∘ᵐ-congʳ
      (≈ᵐ-trans (⟨⟩ᵐ-∘ _ _ _)
      (≈ᵐ-sym (≈ᵐ-trans (mapˣᵐ-∘⟨⟩ h idᵐ idᵐ (s ∘ᵐ h))
                        ⟨ ≈ᵐ-trans (∘ᵐ-identityʳ _) (≈ᵐ-sym (∘ᵐ-identityˡ _))
                        , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congˡ (copairˣᵐ-∘ f g h))))

  caseᵐ-η : ∀ {X A B C} → (s : X →ᵐ A +ᵐ B) → (m : X ×ᵐ (A +ᵐ B) →ᵐ C)
          → m ∘ᵐ ⟨ idᵐ , s ⟩ᵐ
          ≈ᵐ caseᵐ s (m ∘ᵐ mapˣᵐ idᵐ inlᵐ) (m ∘ᵐ mapˣᵐ idᵐ inrᵐ)
  caseᵐ-η s m = ∘ᵐ-congˡ (copairˣᵐ-unique _ _ m ≈ᵐ-refl ≈ᵐ-refl)

  caseᵐ-map+ᵐ : ∀ {X A A' B B' C} → (s : X →ᵐ A' +ᵐ B')
              → (a : A' →ᵐ A) → (b : B' →ᵐ B)
              → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C)
              → caseᵐ (map+ᵐ a b ∘ᵐ s) f g
              ≈ᵐ caseᵐ s (f ∘ᵐ mapˣᵐ idᵐ a) (g ∘ᵐ mapˣᵐ idᵐ b)
  caseᵐ-map+ᵐ s a b f g =
    ≈ᵐ-trans (∘ᵐ-congʳ (⟨⟩ᵐ-mapˣᵐ (map+ᵐ a b) s))
    (≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              (∘ᵐ-congˡ (copairˣᵐ-map+ᵐ f g a b)))

  caseᵐ-post : ∀ {X A B C D} → (s : X →ᵐ A +ᵐ B)
             → (f : X ×ᵐ A →ᵐ C) → (g : X ×ᵐ B →ᵐ C) → (k : C →ᵐ D)
             → k ∘ᵐ caseᵐ s f g ≈ᵐ caseᵐ s (k ∘ᵐ f) (k ∘ᵐ g)
  caseᵐ-post s f g k =
    ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-assoc _ _ _)) (∘ᵐ-congˡ (copairˣᵐ-post f g k))
