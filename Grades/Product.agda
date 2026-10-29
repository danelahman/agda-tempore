------------------------------------------------------------------------
-- The product of two grades, and of two grade systems.               --
--                                                                    --
-- `G₁ ×ᵍ G₂` is the componentwise product: `_·_`, `u`, `⊤`, `_⊔_`    --
-- and the order are those of the components, and `of-dur τ` is       --
-- `(of-dur τ , of-dur τ)`, a delay advancing both components; the    --
-- components share their durations.                                  --
-- Every law holds componentwise, the zero-product laws included, and --
-- the order is decided componentwise. The hints of the product       --
-- declare the unit least, `_·_` commutative and closures where both  --
-- components' hints do.                                              --
--                                                                    --
-- Both projections are grade morphisms, each field of `_→ᵍ_` holding --
-- by `refl`, and pairing of morphisms `⟨ f , g ⟩ᵍ` has the universal --
-- property. The product of two grade systems over the same           --
-- durations pairs the effect grades and the resource grades, with    --
-- the componentwise projection, and its two projections are maps of  --
-- grade systems; its hints are the components', paired.              --
------------------------------------------------------------------------

module Grades.Product where

open import Data.List.Base using (List; concatMap) renaming (map to mapᴸ)
open import Data.Maybe.Base using (Maybe; just; nothing; zipWith)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary.Decidable using (_×-dec_)

open import Grades.Durations
open import Grades.Base
open import Grades.Hints

open import Util.Equality

open Grade using (≃-refl; ≃-trans)

private
  pairᵐ : ∀ {a b c d : Set} → a × b → c × d → (a × c) × (b × d)
  pairᵐ (p , p') (q , q') = (p , q) , (p' , q')

------------------------------------------------------------------------
-- Composition of morphisms

module _ {D : Duration} {G₁ G₂ G₃ : Grade D} where

  open _→ᵍ_

  infixr 9 _∘ᵍ_

  _∘ᵍ_ : G₂ →ᵍ G₃ → G₁ →ᵍ G₂ → G₁ →ᵍ G₃
  g ∘ᵍ f = record
    { map          = λ c → map g (map f c)
    ; map-monotone = λ p → map-monotone g (map-monotone f p)
    ; map-u        = ≃-trans G₃ (map-≃ g (map-u f)) (map-u g)
    ; map-·        = ≃-trans G₃ (map-≃ g (map-· f)) (map-· g)
    ; map-⊤        = ≃-trans G₃ (map-≃ g (map-⊤ f)) (map-⊤ g)
    ; map-⊔        = ≃-trans G₃ (map-≃ g (map-⊔ f)) (map-⊔ g)
    ; map-of-dur   = ≃-trans G₃ (map-≃ g (map-of-dur f)) (map-of-dur g)
    }

------------------------------------------------------------------------
-- The product grade

infixr 2 _×ᵍ_

_×ᵍ_ : {D : Duration} → Grade D → Grade D → Grade D
G₁ ×ᵍ G₂ = record
  { Carrier         = C₁ × C₂
  ; _·_             = λ (c₁ , c₂) (d₁ , d₂) → (c₁ ·₁ d₁ , c₂ ·₂ d₂)
  ; u               = (u₁ , u₂)
  ; _≾_             = λ (c₁ , c₂) (d₁ , d₂) → (c₁ ≾₁ d₁) × (c₂ ≾₂ d₂)
  ; ⊤               = (⊤₁ , ⊤₂)
  ; _⊔_             = λ (c₁ , c₂) (d₁ , d₂) → (c₁ ⊔₁ d₁ , c₂ ⊔₂ d₂)
  ; of-dur          = λ τ → (of-dur₁ τ , of-dur₂ τ)
  ; ·-identityˡ     = λ (c₁ , c₂) → pair≃ (G₁.·-identityˡ c₁) (G₂.·-identityˡ c₂)
  ; ·-identityʳ     = λ (c₁ , c₂) → pair≃ (G₁.·-identityʳ c₁) (G₂.·-identityʳ c₂)
  ; ·-assoc         = λ (c₁ , c₂) (d₁ , d₂) (e₁ , e₂) →
                        pair≃ (G₁.·-assoc c₁ d₁ e₁) (G₂.·-assoc c₂ d₂ e₂)
  ; ≾-refl          = G₁.≾-refl , G₂.≾-refl
  ; ≾-trans         = λ (p₁ , p₂) (q₁ , q₂) → G₁.≾-trans p₁ q₁ , G₂.≾-trans p₂ q₂
  ; ≾-irrelevant    = λ (p₁ , p₂) (q₁ , q₂) →
                        cong₂ _,_ (G₁.≾-irrelevant p₁ q₁) (G₂.≾-irrelevant p₂ q₂)
  ; _≾?_            = λ (c₁ , c₂) (d₁ , d₂) → (c₁ G₁.≾? d₁) ×-dec (c₂ G₂.≾? d₂)
  ; ≾-⊤             = λ (c₁ , c₂) → G₁.≾-⊤ c₁ , G₂.≾-⊤ c₂
  ; ⊔-ubˡ           = λ (c₁ , c₂) (d₁ , d₂) → G₁.⊔-ubˡ c₁ d₁ , G₂.⊔-ubˡ c₂ d₂
  ; ⊔-ubʳ           = λ (c₁ , c₂) (d₁ , d₂) → G₁.⊔-ubʳ c₁ d₁ , G₂.⊔-ubʳ c₂ d₂
  ; ⊔-lub           = λ (p₁ , p₂) (q₁ , q₂) → G₁.⊔-lub p₁ q₁ , G₂.⊔-lub p₂ q₂
  ; ·-monoˡ-≾       = λ (p₁ , p₂) → G₁.·-monoˡ-≾ p₁ , G₂.·-monoˡ-≾ p₂
  ; ·-monoʳ-≾       = λ (p₁ , p₂) → G₁.·-monoʳ-≾ p₁ , G₂.·-monoʳ-≾ p₂
  ; ·-distribˡ-⊔-≾  = λ (c₁ , c₂) (d₁ , d₂) (e₁ , e₂) →
                        G₁.·-distribˡ-⊔-≾ c₁ d₁ e₁ , G₂.·-distribˡ-⊔-≾ c₂ d₂ e₂
  ; ·-distribʳ-⊔-≾  = λ (c₁ , c₂) (d₁ , d₂) (e₁ , e₂) →
                        G₁.·-distribʳ-⊔-≾ c₁ d₁ e₁ , G₂.·-distribʳ-⊔-≾ c₂ d₂ e₂
  ; ≾-zero-productˡ = λ (p₁ , p₂) → G₁.≾-zero-productˡ p₁ , G₂.≾-zero-productˡ p₂
  ; ≾-zero-productʳ = λ (p₁ , p₂) → G₁.≾-zero-productʳ p₁ , G₂.≾-zero-productʳ p₂
  ; of-dur-zero     = pair≃ G₁.of-dur-zero G₂.of-dur-zero
  ; of-dur-plus     = pair≃ G₁.of-dur-plus G₂.of-dur-plus
  ; ≃⇒≡?            = zipWith (λ a₁ a₂ ((p₁ , p₂) , (q₁ , q₂)) → cong₂ _,_ (a₁ (p₁ , q₁)) (a₂ (p₂ , q₂)))
                              G₁.≃⇒≡? G₂.≃⇒≡?
  }
  where
    module G₁ = Grade G₁
    module G₂ = Grade G₂
    pair≃ : ∀ {a a' b b'} → a G₁.≃ a' → b G₂.≃ b'
          → (a G₁.≾ a' × b G₂.≾ b') × (a' G₁.≾ a × b' G₂.≾ b)
    pair≃ (p , p') (q , q') = (p , q) , (p' , q')
    open Grade G₁ using () renaming (Carrier to C₁; _·_ to _·₁_; u to u₁;
      _≾_ to _≾₁_; ⊤ to ⊤₁; _⊔_ to _⊔₁_; of-dur to of-dur₁)
    open Grade G₂ using () renaming (Carrier to C₂; _·_ to _·₂_; u to u₂;
      _≾_ to _≾₂_; ⊤ to ⊤₂; _⊔_ to _⊔₂_; of-dur to of-dur₂)

-- its hints, componentwise

infixr 2 _×ʰ_

_×ʰ_ : {D : Duration} {G₁ G₂ : Grade D} → GradeHints G₁ → GradeHints G₂ → GradeHints (G₁ ×ᵍ G₂)
_×ʰ_ {G₁ = G₁} {G₂} H₁ H₂ = record
  { u-least? = zipWith (λ l₁ l₂ (c₁ , c₂) → l₁ c₁ , l₂ c₂) H₁.u-least? H₂.u-least?
  ; ·-comm?  = zipWith (λ m₁ m₂ (c₁ , c₂) (d₁ , d₂) → pairᵐ (m₁ c₁ d₁) (m₂ c₂ d₂))
                       H₁.·-comm? H₂.·-comm?
  ; plus?    = λ (c₁ , c₂) → zipWith plus× (H₁.plus? c₁) (H₂.plus? c₂)
  }
  where
    module H₁ = GradeHints H₁
    module H₂ = GradeHints H₂
    open Grade G₁ using () renaming (_·_ to _·₁_; _≾_ to _≾₁_)
    open Grade G₂ using () renaming (_·_ to _·₂_; _≾_ to _≾₂_)

    -- the closure, componentwise
    plus× : ∀ {c₁ c₂} → Plus _·₁_ _≾₁_ c₁ → Plus _·₂_ _≾₂_ c₂
          → Plus (λ (c₁ , c₂) (d₁ , d₂) → (c₁ ·₁ d₁ , c₂ ·₂ d₂))
                 (λ (c₁ , c₂) (d₁ , d₂) → (c₁ ≾₁ d₁) × (c₂ ≾₂ d₂)) (c₁ , c₂)
    plus× p₁ p₂ =
      plus (Plus.c⁺ p₁ , Plus.c⁺ p₂) (Plus.≾-c⁺ p₁ , Plus.≾-c⁺ p₂)
           (Plus.c⁺-iter p₁ , Plus.c⁺-iter p₂)
           (λ (a₁ , a₂) (b₁ , b₂) → Plus.c⁺-least p₁ a₁ b₁ , Plus.c⁺-least p₂ a₂ b₂)
           (λ (a₁ , a₂) → Plus.⁺-indˡ p₁ a₁ , Plus.⁺-indˡ p₂ a₂)
           (λ (a₁ , a₂) → Plus.⁺-indʳ p₁ a₁ , Plus.⁺-indʳ p₂ a₂)

------------------------------------------------------------------------
-- The projections and pairing

module _ {D : Duration} {G₁ G₂ : Grade D} where

  π₁ᵍ : (G₁ ×ᵍ G₂) →ᵍ G₁
  π₁ᵍ = record
    { map          = proj₁
    ; map-monotone = proj₁
    ; map-u        = ≃-refl G₁
    ; map-·        = ≃-refl G₁
    ; map-⊤        = ≃-refl G₁
    ; map-⊔        = ≃-refl G₁
    ; map-of-dur   = ≃-refl G₁
    }

  π₂ᵍ : (G₁ ×ᵍ G₂) →ᵍ G₂
  π₂ᵍ = record
    { map          = proj₂
    ; map-monotone = proj₂
    ; map-u        = ≃-refl G₂
    ; map-·        = ≃-refl G₂
    ; map-⊤        = ≃-refl G₂
    ; map-⊔        = ≃-refl G₂
    ; map-of-dur   = ≃-refl G₂
    }

module _ {D : Duration} {G G₁ G₂ : Grade D} where

  open _→ᵍ_

  ⟨_,_⟩ᵍ : G →ᵍ G₁ → G →ᵍ G₂ → G →ᵍ (G₁ ×ᵍ G₂)
  ⟨ f , g ⟩ᵍ = record
    { map          = λ c → (map f c , map g c)
    ; map-monotone = λ p → map-monotone f p , map-monotone g p
    ; map-u        = pairᵐ (map-u f) (map-u g)
    ; map-·        = pairᵐ (map-· f) (map-· g)
    ; map-⊤        = pairᵐ (map-⊤ f) (map-⊤ g)
    ; map-⊔        = pairᵐ (map-⊔ f) (map-⊔ g)
    ; map-of-dur   = pairᵐ (map-of-dur f) (map-of-dur g)
    }

  -- the universal property: pairing followed by a projection is the
  -- component, and a map into the product is the pairing of its
  -- components

  π₁ᵍ-⟨⟩ : (f : G →ᵍ G₁) (g : G →ᵍ G₂) (c : Grade.Carrier G)
         → map (π₁ᵍ {G₁ = G₁} {G₂ = G₂}) (map ⟨ f , g ⟩ᵍ c) ≡ map f c
  π₁ᵍ-⟨⟩ f g c = refl

  π₂ᵍ-⟨⟩ : (f : G →ᵍ G₁) (g : G →ᵍ G₂) (c : Grade.Carrier G)
         → map (π₂ᵍ {G₁ = G₁} {G₂ = G₂}) (map ⟨ f , g ⟩ᵍ c) ≡ map g c
  π₂ᵍ-⟨⟩ f g c = refl

  ⟨⟩ᵍ-unique : (h : G →ᵍ (G₁ ×ᵍ G₂)) (c : Grade.Carrier G)
             → map h c ≡ map ⟨ π₁ᵍ {G₁ = G₁} {G₂ = G₂} ∘ᵍ h , π₂ᵍ {G₁ = G₁} {G₂ = G₂} ∘ᵍ h ⟩ᵍ c
  ⟨⟩ᵍ-unique h c = refl

-- the product of two morphisms, acting componentwise

module _ {D : Duration} {G₁ G₂ H₁ H₂ : Grade D} where

  open _→ᵍ_

  _×ᵐ_ : G₁ →ᵍ H₁ → G₂ →ᵍ H₂ → (G₁ ×ᵍ G₂) →ᵍ (H₁ ×ᵍ H₂)
  f ×ᵐ g = record
    { map          = λ (c₁ , c₂) → (map f c₁ , map g c₂)
    ; map-monotone = λ (p₁ , p₂) → map-monotone f p₁ , map-monotone g p₂
    ; map-u        = pairᵐ (map-u f) (map-u g)
    ; map-·        = pairᵐ (map-· f) (map-· g)
    ; map-⊤        = pairᵐ (map-⊤ f) (map-⊤ g)
    ; map-⊔        = pairᵐ (map-⊔ f) (map-⊔ g)
    ; map-of-dur   = pairᵐ (map-of-dur f) (map-of-dur g)
    }

------------------------------------------------------------------------
-- Maps of grade systems
--
-- A morphism of the durations, and along it a morphism on the effect
-- grades and one on the resource grades, commuting with the
-- projections `∣_∣ᵉ`.

record _→ˢ_ (S₁ S₂ : GradeSystem) : Set₁ where
  open GradeSystem
  open GradeMorphism

  field
    mapᴰ   : Dur S₁ →ᴰ Dur S₂
    mapᴱ   : GradeMorphism mapᴰ (EGrade S₁) (EGrade S₂)
    mapᴿ   : GradeMorphism mapᴰ (RGrade S₁) (RGrade S₂)
    square : (e : Grade.Carrier (EGrade S₁))
           → map ∣ S₂ ∣ᵉ (map mapᴱ e) ≡ map mapᴿ (map ∣ S₁ ∣ᵉ e)

------------------------------------------------------------------------
-- Candidate grades of a product: each candidate of the first component
-- paired with each of the second, from the constants' components

pairs : {A B : Set} → List A → List B → List (A × B)
pairs as bs = concatMap (λ a → mapᴸ (a ,_) bs) as

_×ʷ_ : {A B : Set} → (ℕ → List A → List A) → (ℕ → List B → List B) → ℕ → List (A × B) → List (A × B)
(w₁ ×ʷ w₂) d cs = pairs (w₁ d (mapᴸ proj₁ cs)) (w₂ d (mapᴸ proj₂ cs))

------------------------------------------------------------------------
-- The product of two grade systems over the same durations

infixr 2 _×ˢ_⟨_⟩

_×ˢ_⟨_⟩ : (S₁ S₂ : GradeSystem)
        → GradeSystem.Dur S₁ ≡ GradeSystem.Dur S₂ → GradeSystem
record { Dur = D ; RGrade = R₁ ; EGrade = E₁ ; ∣_∣ᵉ = p₁ }
  ×ˢ record { RGrade = R₂ ; EGrade = E₂ ; ∣_∣ᵉ = p₂ } ⟨ refl ⟩ = record
  { Dur    = D
  ; RGrade = R₁ ×ᵍ R₂
  ; EGrade = E₁ ×ᵍ E₂
  ; ∣_∣ᵉ   = p₁ ×ᵐ p₂
  }

-- its hints: it reflects the order at the unit where both components
-- do, and its candidates are pairs of the components'

infixr 2 _×ʰˢ_⟨_⟩

_×ʰˢ_⟨_⟩ : {S₁ S₂ : GradeSystem} → SystemHints S₁ → SystemHints S₂
         → (e : GradeSystem.Dur S₁ ≡ GradeSystem.Dur S₂) → SystemHints (S₁ ×ˢ S₂ ⟨ e ⟩)
_×ʰˢ_⟨_⟩ {record { Dur = D }} {record {}} H₁ H₂ refl = record
  { RHints      = H₁.RHints ×ʰ H₂.RHints
  ; EHints      = H₁.EHints ×ʰ H₂.EHints
  ; reflects-u? = zipWith (λ f g (e₁ , e₂) (q₁ , q₂) → f e₁ q₁ , g e₂ q₂) H₁.reflects-u? H₂.reflects-u?
  ; witnesses   = λ d rcs ecs → pairs (H₁.witnesses d (mapᴸ proj₁ rcs) (mapᴸ proj₁ ecs))
                                      (H₂.witnesses d (mapᴸ proj₂ rcs) (mapᴸ proj₂ ecs))
  }
  where
    module H₁ = SystemHints H₁
    module H₂ = SystemHints H₂

-- its projections are maps of grade systems, the squares commuting on
-- the nose

π₁ˢ : (S₁ S₂ : GradeSystem) (e : GradeSystem.Dur S₁ ≡ GradeSystem.Dur S₂)
    → (S₁ ×ˢ S₂ ⟨ e ⟩) →ˢ S₁
π₁ˢ record { RGrade = R₁ ; EGrade = E₁ }
    record { RGrade = R₂ ; EGrade = E₂ } refl =
  record { mapᴰ = idᴰ
         ; mapᴱ = π₁ᵍ {G₁ = E₁} {E₂}
         ; mapᴿ = π₁ᵍ {G₁ = R₁} {R₂}
         ; square = λ _ → refl }

π₂ˢ : (S₁ S₂ : GradeSystem) (e : GradeSystem.Dur S₁ ≡ GradeSystem.Dur S₂)
    → (S₁ ×ˢ S₂ ⟨ e ⟩) →ˢ S₂
π₂ˢ record { RGrade = R₁ ; EGrade = E₁ }
    record { RGrade = R₂ ; EGrade = E₂ } refl =
  record { mapᴰ = idᴰ
         ; mapᴱ = π₂ᵍ {G₁ = E₁} {E₂}
         ; mapᴿ = π₂ᵍ {G₁ = R₁} {R₂}
         ; square = λ _ → refl }
