------------------------------------------------------------------------
-- The product of two grades, and of two grade systems.               --
--                                                                    --
-- `G₁ ×ᵍ G₂` is the componentwise product: `_·_`, `u`, `⊤`, `_⊔_`    --
-- and the order are those of the components, and `of-nat n` is       --
-- `(of-nat n , of-nat n)`, a time step advancing both components.    --
-- Every law holds componentwise, the zero-product laws included, and --
-- the order is decided componentwise. `u-least?` and `·-comm?` are   --
-- declared when both components declare them.                        --
--                                                                    --
-- Both projections are grade morphisms, each field of `_→ᵍ_` holding --
-- by `refl`, and pairing of morphisms `⟨ f , g ⟩ᵍ` has the universal --
-- property. The product of two grade systems pairs the effect grades --
-- and the resource grades, with the componentwise projection, and    --
-- its two projections are maps of grade systems.                     --
------------------------------------------------------------------------

module Syntax.Grades.Product where

open import Data.Maybe.Base using (Maybe; just; nothing; zipWith)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary.Decidable using (_×-dec_)

open import Syntax.Grades

open import Util.Equality

------------------------------------------------------------------------
-- Composition of morphisms

module _ {G₁ G₂ G₃ : Grade} where

  open _→ᵍ_

  infixr 9 _∘ᵍ_

  _∘ᵍ_ : G₂ →ᵍ G₃ → G₁ →ᵍ G₂ → G₁ →ᵍ G₃
  g ∘ᵍ f = record
    { map          = λ c → map g (map f c)
    ; map-monotone = λ p → map-monotone g (map-monotone f p)
    ; map-u        = trans (cong (map g) (map-u f)) (map-u g)
    ; map-·        = trans (cong (map g) (map-· f)) (map-· g)
    ; map-⊤        = trans (cong (map g) (map-⊤ f)) (map-⊤ g)
    ; map-⊔        = trans (cong (map g) (map-⊔ f)) (map-⊔ g)
    ; map-of-nat   = trans (cong (map g) (map-of-nat f)) (map-of-nat g)
    }

------------------------------------------------------------------------
-- The product grade

infixr 2 _×ᵍ_

_×ᵍ_ : Grade → Grade → Grade
G₁ ×ᵍ G₂ = record
  { Carrier         = C₁ × C₂
  ; _·_             = λ (c₁ , c₂) (d₁ , d₂) → (c₁ ·₁ d₁ , c₂ ·₂ d₂)
  ; u               = (u₁ , u₂)
  ; _≾_             = λ (c₁ , c₂) (d₁ , d₂) → (c₁ ≾₁ d₁) × (c₂ ≾₂ d₂)
  ; ⊤               = (⊤₁ , ⊤₂)
  ; _⊔_             = λ (c₁ , c₂) (d₁ , d₂) → (c₁ ⊔₁ d₁ , c₂ ⊔₂ d₂)
  ; of-nat          = λ n → (of-nat₁ n , of-nat₂ n)
  ; ·-identityˡ     = λ (c₁ , c₂) → cong₂ _,_ (G₁.·-identityˡ c₁) (G₂.·-identityˡ c₂)
  ; ·-identityʳ     = λ (c₁ , c₂) → cong₂ _,_ (G₁.·-identityʳ c₁) (G₂.·-identityʳ c₂)
  ; ·-assoc         = λ (c₁ , c₂) (d₁ , d₂) (e₁ , e₂) →
                        cong₂ _,_ (G₁.·-assoc c₁ d₁ e₁) (G₂.·-assoc c₂ d₂ e₂)
  ; ≾-refl          = G₁.≾-refl , G₂.≾-refl
  ; ≾-trans         = λ (p₁ , p₂) (q₁ , q₂) → G₁.≾-trans p₁ q₁ , G₂.≾-trans p₂ q₂
  ; ≾-antisym       = λ (p₁ , p₂) (q₁ , q₂) →
                        cong₂ _,_ (G₁.≾-antisym p₁ q₁) (G₂.≾-antisym p₂ q₂)
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
  ; of-nat-zero     = cong₂ _,_ G₁.of-nat-zero G₂.of-nat-zero
  ; of-nat-plus     = cong₂ _,_ G₁.of-nat-plus G₂.of-nat-plus
  ; u-least?        = zipWith (λ l₁ l₂ (c₁ , c₂) → l₁ c₁ , l₂ c₂)
                              G₁.u-least? G₂.u-least?
  ; ·-comm?         = zipWith (λ m₁ m₂ (c₁ , c₂) (d₁ , d₂) →
                                 cong₂ _,_ (m₁ c₁ d₁) (m₂ c₂ d₂))
                              G₁.·-comm? G₂.·-comm?
  }
  where
    module G₁ = Grade G₁
    module G₂ = Grade G₂
    open Grade G₁ using () renaming (Carrier to C₁; _·_ to _·₁_; u to u₁;
      _≾_ to _≾₁_; ⊤ to ⊤₁; _⊔_ to _⊔₁_; of-nat to of-nat₁)
    open Grade G₂ using () renaming (Carrier to C₂; _·_ to _·₂_; u to u₂;
      _≾_ to _≾₂_; ⊤ to ⊤₂; _⊔_ to _⊔₂_; of-nat to of-nat₂)

------------------------------------------------------------------------
-- The projections and pairing

module _ {G₁ G₂ : Grade} where

  π₁ᵍ : (G₁ ×ᵍ G₂) →ᵍ G₁
  π₁ᵍ = record
    { map          = proj₁
    ; map-monotone = proj₁
    ; map-u        = refl
    ; map-·        = refl
    ; map-⊤        = refl
    ; map-⊔        = refl
    ; map-of-nat   = refl
    }

  π₂ᵍ : (G₁ ×ᵍ G₂) →ᵍ G₂
  π₂ᵍ = record
    { map          = proj₂
    ; map-monotone = proj₂
    ; map-u        = refl
    ; map-·        = refl
    ; map-⊤        = refl
    ; map-⊔        = refl
    ; map-of-nat   = refl
    }

module _ {G G₁ G₂ : Grade} where

  open _→ᵍ_

  ⟨_,_⟩ᵍ : G →ᵍ G₁ → G →ᵍ G₂ → G →ᵍ (G₁ ×ᵍ G₂)
  ⟨ f , g ⟩ᵍ = record
    { map          = λ c → (map f c , map g c)
    ; map-monotone = λ p → map-monotone f p , map-monotone g p
    ; map-u        = cong₂ _,_ (map-u f) (map-u g)
    ; map-·        = cong₂ _,_ (map-· f) (map-· g)
    ; map-⊤        = cong₂ _,_ (map-⊤ f) (map-⊤ g)
    ; map-⊔        = cong₂ _,_ (map-⊔ f) (map-⊔ g)
    ; map-of-nat   = cong₂ _,_ (map-of-nat f) (map-of-nat g)
    }

  -- the universal property: pairing followed by a projection is the
  -- component, and a map into the product is the pairing of its
  -- components

  π₁ᵍ-⟨⟩ : (f : G →ᵍ G₁) (g : G →ᵍ G₂) (c : Grade.Carrier G)
         → map (π₁ᵍ {G₁} {G₂}) (map ⟨ f , g ⟩ᵍ c) ≡ map f c
  π₁ᵍ-⟨⟩ f g c = refl

  π₂ᵍ-⟨⟩ : (f : G →ᵍ G₁) (g : G →ᵍ G₂) (c : Grade.Carrier G)
         → map (π₂ᵍ {G₁} {G₂}) (map ⟨ f , g ⟩ᵍ c) ≡ map g c
  π₂ᵍ-⟨⟩ f g c = refl

  ⟨⟩ᵍ-unique : (h : G →ᵍ (G₁ ×ᵍ G₂)) (c : Grade.Carrier G)
             → map h c ≡ map ⟨ π₁ᵍ {G₁} {G₂} ∘ᵍ h , π₂ᵍ {G₁} {G₂} ∘ᵍ h ⟩ᵍ c
  ⟨⟩ᵍ-unique h c = refl

-- the product of two morphisms, acting componentwise

module _ {G₁ G₂ H₁ H₂ : Grade} where

  open _→ᵍ_

  _×ᵐ_ : G₁ →ᵍ H₁ → G₂ →ᵍ H₂ → (G₁ ×ᵍ G₂) →ᵍ (H₁ ×ᵍ H₂)
  f ×ᵐ g = record
    { map          = λ (c₁ , c₂) → (map f c₁ , map g c₂)
    ; map-monotone = λ (p₁ , p₂) → map-monotone f p₁ , map-monotone g p₂
    ; map-u        = cong₂ _,_ (map-u f) (map-u g)
    ; map-·        = cong₂ _,_ (map-· f) (map-· g)
    ; map-⊤        = cong₂ _,_ (map-⊤ f) (map-⊤ g)
    ; map-⊔        = cong₂ _,_ (map-⊔ f) (map-⊔ g)
    ; map-of-nat   = cong₂ _,_ (map-of-nat f) (map-of-nat g)
    }

------------------------------------------------------------------------
-- Maps of grade systems
--
-- A morphism on the effect grades and one on the resource grades,
-- commuting with the projections `∣_∣ᵉ`.

record _→ˢ_ (S₁ S₂ : GradeSystem) : Set₁ where
  open GradeSystem
  open _→ᵍ_

  field
    mapᴱ   : EGrade S₁ →ᵍ EGrade S₂
    mapᴿ   : RGrade S₁ →ᵍ RGrade S₂
    square : (e : Grade.Carrier (EGrade S₁))
           → map ∣ S₂ ∣ᵉ (map mapᴱ e) ≡ map mapᴿ (map ∣ S₁ ∣ᵉ e)

------------------------------------------------------------------------
-- The product of two grade systems

infixr 2 _×ˢ_

_×ˢ_ : GradeSystem → GradeSystem → GradeSystem
S₁ ×ˢ S₂ = record
  { RGrade = RGrade S₁ ×ᵍ RGrade S₂
  ; EGrade = EGrade S₁ ×ᵍ EGrade S₂
  ; ∣_∣ᵉ   = ∣ S₁ ∣ᵉ ×ᵐ ∣ S₂ ∣ᵉ
  }
  where open GradeSystem

-- its projections are maps of grade systems, the squares commuting on
-- the nose

module _ {S₁ S₂ : GradeSystem} where

  open GradeSystem

  π₁ˢ : (S₁ ×ˢ S₂) →ˢ S₁
  π₁ˢ = record { mapᴱ = π₁ᵍ {EGrade S₁} {EGrade S₂}
                ; mapᴿ = π₁ᵍ {RGrade S₁} {RGrade S₂}
                ; square = λ _ → refl }

  π₂ˢ : (S₁ ×ˢ S₂) →ˢ S₂
  π₂ˢ = record { mapᴱ = π₂ᵍ {EGrade S₁} {EGrade S₂}
                ; mapᴿ = π₂ᵍ {RGrade S₁} {RGrade S₂}
                ; square = λ _ → refl }
