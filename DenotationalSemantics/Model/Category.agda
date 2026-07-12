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

  -- associator of the product (and its inverse)

  ×ᵐ-assoc : ∀ {A B C} → (A ×ᵐ B) ×ᵐ C →ᵐ A ×ᵐ (B ×ᵐ C)
  ×ᵐ-assoc = ⟨ fstᵐ ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

  ×ᵐ-assoc⁻¹ : ∀ {A B C} → A ×ᵐ (B ×ᵐ C) →ᵐ (A ×ᵐ B) ×ᵐ C
  ×ᵐ-assoc⁻¹ = ⟨ ⟨ fstᵐ , fstᵐ ∘ᵐ sndᵐ ⟩ᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ

  -- SET-INDEXED PRODUCTS (used to package a handler as an object of
  -- operation clauses)

  field
    Πᵐ : (I : Set) → (I → Obj) → Obj

    projᵐ : ∀ {I A} → (i : I) → Πᵐ I A →ᵐ A i
    ⟨_⟩ᵢᵐ : ∀ {I A B} → ((i : I) → A →ᵐ B i) → A →ᵐ Πᵐ I B

    ⟨⟩ᵢᵐ-cong : ∀ {I A} {B : I → Obj} {f g : (i : I) → A →ᵐ B i}
              → (∀ i → f i ≈ᵐ g i) → ⟨ f ⟩ᵢᵐ ≈ᵐ ⟨ g ⟩ᵢᵐ
    ⟨⟩ᵢᵐ-projᵐ : ∀ {I A} {B : I → Obj} → (f : (i : I) → A →ᵐ B i) → (i : I)
               → projᵐ i ∘ᵐ ⟨ f ⟩ᵢᵐ ≈ᵐ f i
    ⟨⟩ᵢᵐ-unique : ∀ {I A} {B : I → Obj} → (f : (i : I) → A →ᵐ B i) → (g : A →ᵐ Πᵐ I B)
                → ((i : I) → projᵐ i ∘ᵐ g ≈ᵐ f i) → g ≈ᵐ ⟨ f ⟩ᵢᵐ

  -- functorial action of the set-indexed product

  mapⁱˣᵐ : ∀ {I} {A B : I → Obj} → ((i : I) → A i →ᵐ B i) → Πᵐ I A →ᵐ Πᵐ I B
  mapⁱˣᵐ f = ⟨ (λ i → f i ∘ᵐ projᵐ i) ⟩ᵢᵐ

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
