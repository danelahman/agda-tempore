--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Grades.Base where

open import Data.Empty
open import Data.Product hiding (map)
open import Data.Sum hiding (map)

open import Level hiding (_⊔_) renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Grades.Durations

open import Util.Equality

-- The closure of `c`, Kleene's plus: the least grade above `c` that
-- absorbs its own iteration; a grade that `c` does not move, on either
-- side, `c⁺` does not move either (induction)

record Plus {C : Set} (_·_ : C → C → C) (_≾_ : C → C → Set) (c : C) : Set where
  constructor plus
  field
    c⁺       : C
    ≾-c⁺     : c ≾ c⁺
    c⁺-iter  : (c⁺ · c⁺) ≾ c⁺
    c⁺-least : ∀ {v} → c ≾ v → (v · v) ≾ v → c⁺ ≾ v
    ⁺-indˡ   : ∀ {d} → (c · d) ≾ d → (c⁺ · d) ≾ d
    ⁺-indʳ   : ∀ {d} → (d · c) ≾ d → (d · c⁺) ≾ d

-- A grade absorbing its own iteration is its own closure

plus-self : ∀ {C : Set} {_·_ : C → C → C} {_≾_ : C → C → Set} {c : C}
          → c ≾ c → (c · c) ≾ c → Plus _·_ _≾_ c
plus-self {c = c} refl' it = plus c refl' it (λ cv _ → cv) (λ q → q) (λ q → q)

-- Preordered effect and resource monoids, over a monoid `D` of
-- durations. Equality of grades is the order's equivalence
--
--   c ≃ d   =   c ≾ d × d ≾ c
--
-- and the monoid laws and the inclusion of durations hold up to it. A
-- grade is its structure and laws; the solver's hints for a grade are
-- in `Grades.Hints`.

record Grade (D : Duration) : Set₁ where
  private
    module D = Duration D

  infixl 7 _·_
  infixl 6 _⊔_
  infixl 5 _≾_
  infix  4 _≃_

  field

    -- carrier and operations
    Carrier : Set₀
    _≾_     : Rel Carrier lzero
    𝟏       : Carrier
    _·_     : Carrier → Carrier → Carrier
    ⊤       : Carrier
    _⊔_     : Carrier → Carrier → Carrier
    ι       : D.Carrier → Carrier

  -- equality is the order's equivalence
  _≃_ : Rel Carrier lzero
  c ≃ d = (c ≾ d) × (d ≾ c)

  field

    -- a monoid, up to equivalence
    ·-identityˡ : (c : Carrier) → (𝟏 · c) ≃ c
    ·-identityʳ : (c : Carrier) → (c · 𝟏) ≃ c
    ·-assoc     : (c d e : Carrier) → (c · d) · e ≃ c · (d · e)

    -- a preorder, decidable and proof-irrelevant
    ≾-refl       : Reflexive _≾_
    ≾-trans      : Transitive _≾_
    ≾-irrelevant : ∀ {c d} → (p q : c ≾ d) → p ≡ q
    _≾?_         : Decidable _≾_

    -- ⊤ is the greatest grade
    ≾-⊤ : (c : Carrier) → c ≾ ⊤

    -- ⊔ is a binary join
    ⊔-ubˡ : (c d : Carrier) → c ≾ c ⊔ d
    ⊔-ubʳ : (c d : Carrier) → d ≾ c ⊔ d
    ⊔-lub : {c d e : Carrier} → c ≾ e → d ≾ e → c ⊔ d ≾ e

    -- an ordered monoid; · distributes over ⊔ (the converse
    -- inequalities follow from monotonicity)
    ·-monoˡ-≾      : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
    ·-monoʳ-≾      : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_
    ·-distribˡ-⊔-≾ : (c d e : Carrier) → c · (d ⊔ e) ≾ (c · d) ⊔ (c · e)
    ·-distribʳ-⊔-≾ : (c d e : Carrier) → (d ⊔ e) · c ≾ (d · c) ⊔ (e · c)

    -- the unit's zero-product property
    ≾-zero-productˡ : ∀ {c d} → c · d ≾ 𝟏 → c ≾ 𝟏
    ≾-zero-productʳ : ∀ {c d} → c · d ≾ 𝟏 → d ≾ 𝟏

    -- durations included as a monoid morphism up to equivalence,
    -- `ι τ` the grade of the delay `τ`
    ι-zero : ι D.0ᴰ ≃ 𝟏
    ι-plus : ∀ {τ τ'} → ι (τ D.+ᴰ τ') ≃ ι τ · ι τ'

  -- _≡_ is included in _≾_
  ≾-reflexive  : _≡_ ⇒ _≾_
  ≾-reflexive refl = ≾-refl

  -- _≃_ is a proof-irrelevant equivalence including _≡_
  ≃-refl : ∀ {c} → c ≃ c
  ≃-refl = ≾-refl , ≾-refl

  ≃-sym : ∀ {c d} → c ≃ d → d ≃ c
  ≃-sym e = proj₂ e , proj₁ e

  ≃-trans : ∀ {c d e} → c ≃ d → d ≃ e → c ≃ e
  ≃-trans e e' = ≾-trans (proj₁ e) (proj₁ e') , ≾-trans (proj₂ e') (proj₂ e)

  ≃-reflexive : _≡_ ⇒ _≃_
  ≃-reflexive refl = ≃-refl

  ≃⇒≾ : ∀ {c d} → c ≃ d → c ≾ d
  ≃⇒≾ = proj₁

  ≃⇒≿ : ∀ {c d} → c ≃ d → d ≾ c
  ≃⇒≿ = proj₂

  ≃-irrelevant : ∀ {c d} → (p q : c ≃ d) → p ≡ q
  ≃-irrelevant (p , q) (p' , q') =
    cong₂ _,_ (≾-irrelevant p p') (≾-irrelevant q q')

  -- _≃_ is decidable
  _≃?_ : Decidable _≃_
  c ≃? d with c ≾? d | d ≾? c
  ... | yes p | yes q = yes (p , q)
  ... | yes _ | no ¬q = no λ r → ¬q (proj₂ r)
  ... | no ¬p | _     = no λ r → ¬p (proj₁ r)

  -- _·_ is a congruence for _≃_
  ·-cong : ∀ {c c' d d'} → c ≃ c' → d ≃ d' → c · d ≃ c' · d'
  ·-cong a b =
    ≾-trans (·-monoˡ-≾ (proj₁ a)) (·-monoʳ-≾ (proj₁ b)) , ≾-trans (·-monoˡ-≾ (proj₂ a)) (·-monoʳ-≾ (proj₂ b))

  -- _⊔_ is monotone with respect to _≾_
  ⊔-mono : ∀ {c c' d d'} → c ≾ c' → d ≾ d' → c ⊔ d ≾ c' ⊔ d'
  ⊔-mono {c' = c'} {d' = d'} p q =
    ⊔-lub (≾-trans p (⊔-ubˡ c' d')) (≾-trans q (⊔-ubʳ c' d'))

  -- _⊔_ is a congruence for _≃_
  ⊔-cong : ∀ {c c' d d'} → c ≃ c' → d ≃ d' → c ⊔ d ≃ c' ⊔ d'
  ⊔-cong a b = ⊔-mono (proj₁ a) (proj₁ b) , ⊔-mono (proj₂ a) (proj₂ b)

  -- _⊔_ is idempotent, commutative and associative: each direction is
  -- a least upper bound
  ⊔-idem : (c : Carrier) → c ⊔ c ≃ c
  ⊔-idem c = ⊔-lub ≾-refl ≾-refl , ⊔-ubˡ c c

  ⊔-comm : (c d : Carrier) → c ⊔ d ≃ d ⊔ c
  ⊔-comm c d = ⊔-lub (⊔-ubʳ d c) (⊔-ubˡ d c) , ⊔-lub (⊔-ubʳ c d) (⊔-ubˡ c d)

  ⊔-assoc : (c d e : Carrier) → (c ⊔ d) ⊔ e ≃ c ⊔ (d ⊔ e)
  ⊔-assoc c d e =
      ⊔-lub (⊔-lub (⊔-ubˡ c (d ⊔ e))
                   (≾-trans (⊔-ubˡ d e) (⊔-ubʳ c (d ⊔ e))))
            (≾-trans (⊔-ubʳ d e) (⊔-ubʳ c (d ⊔ e)))
    , ⊔-lub (≾-trans (⊔-ubˡ c d) (⊔-ubˡ (c ⊔ d) e))
            (⊔-lub (≾-trans (⊔-ubʳ c d) (⊔-ubˡ (c ⊔ d) e))
                   (⊔-ubʳ (c ⊔ d) e))

  -- a grade below another is absorbed by it in a join
  ⊔-absorb : ∀ {c d} → c ≾ d → c ⊔ d ≃ d
  ⊔-absorb {c} {d} p = ⊔-lub p ≾-refl , ⊔-ubʳ c d

  -- ⊤ absorbs joins
  ⊔-⊤ : (c : Carrier) → c ⊔ ⊤ ≃ ⊤
  ⊔-⊤ c = ⊔-absorb (≾-⊤ c)

  -- `_·_` distributes over `_⊔_`: the converse of each field follows
  -- from `_·_` being monotone in each argument separately
  ·-distribˡ-⊔ : (c d e : Carrier) → c · (d ⊔ e) ≃ (c · d) ⊔ (c · e)
  ·-distribˡ-⊔ c d e =
    ·-distribˡ-⊔-≾ c d e , ⊔-lub (·-monoʳ-≾ (⊔-ubˡ d e)) (·-monoʳ-≾ (⊔-ubʳ d e))

  ·-distribʳ-⊔ : (c d e : Carrier) → (d ⊔ e) · c ≃ (d · c) ⊔ (e · c)
  ·-distribʳ-⊔ c d e =
    ·-distribʳ-⊔-≾ c d e , ⊔-lub (·-monoˡ-≾ (⊔-ubˡ d e)) (·-monoˡ-≾ (⊔-ubʳ d e))

open Grade


-- Partially ordered grades: the laws on the nose, with antisymmetry. Each
-- is a grade, its equivalence then coinciding with equality.

record PosetGrade (D : Duration) : Set₁ where
  private
    module D = Duration D

  field
    Carrier : Set₀
    _≾_     : Rel Carrier lzero
    𝟏       : Carrier
    _·_     : Carrier → Carrier → Carrier
    ⊤       : Carrier
    _⊔_     : Carrier → Carrier → Carrier
    ι       : D.Carrier → Carrier

    ·-identityˡ : (c : Carrier) → (𝟏 · c) ≡ c
    ·-identityʳ : (c : Carrier) → (c · 𝟏) ≡ c
    ·-assoc     : (c d e : Carrier) → ((c · d) · e) ≡ (c · (d · e))

    ≾-refl       : Reflexive _≾_
    ≾-trans      : Transitive _≾_
    ≾-antisym    : {c d : Carrier} → c ≾ d → d ≾ c → c ≡ d
    ≾-irrelevant : ∀ {c d} → (p q : c ≾ d) → p ≡ q
    _≾?_         : Decidable _≾_

    ≾-⊤ : (c : Carrier) → c ≾ ⊤

    ⊔-ubˡ : (c d : Carrier) → c ≾ (c ⊔ d)
    ⊔-ubʳ : (c d : Carrier) → d ≾ (c ⊔ d)
    ⊔-lub : {c d e : Carrier} → c ≾ e → d ≾ e → (c ⊔ d) ≾ e

    ·-monoˡ-≾      : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
    ·-monoʳ-≾      : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_
    ·-distribˡ-⊔-≾ : (c d e : Carrier) → (c · (d ⊔ e)) ≾ ((c · d) ⊔ (c · e))
    ·-distribʳ-⊔-≾ : (c d e : Carrier) → ((d ⊔ e) · c) ≾ ((d · c) ⊔ (e · c))

    ≾-zero-productˡ : ∀ {c d} → (c · d) ≾ 𝟏 → c ≾ 𝟏
    ≾-zero-productʳ : ∀ {c d} → (c · d) ≾ 𝟏 → d ≾ 𝟏

    ι-zero : ι D.0ᴰ ≡ 𝟏
    ι-plus : ∀ {τ τ'} → ι (τ D.+ᴰ τ') ≡ (ι τ · ι τ')

posetᵍ : {D : Duration} → PosetGrade D → Grade D
posetᵍ G = record
  { Carrier = P.Carrier ; _≾_ = P._≾_ ; 𝟏 = P.𝟏 ; _·_ = P._·_ ; ⊤ = P.⊤
  ; _⊔_ = P._⊔_ ; ι = P.ι
  ; ·-identityˡ = λ c → ≡⇒≃ (P.·-identityˡ c)
  ; ·-identityʳ = λ c → ≡⇒≃ (P.·-identityʳ c)
  ; ·-assoc = λ c d e → ≡⇒≃ (P.·-assoc c d e)
  ; ≾-refl = P.≾-refl ; ≾-trans = P.≾-trans ; ≾-irrelevant = P.≾-irrelevant
  ; _≾?_ = P._≾?_ ; ≾-⊤ = P.≾-⊤ ; ⊔-ubˡ = P.⊔-ubˡ ; ⊔-ubʳ = P.⊔-ubʳ
  ; ⊔-lub = P.⊔-lub
  ; ·-monoˡ-≾ = P.·-monoˡ-≾ ; ·-monoʳ-≾ = P.·-monoʳ-≾
  ; ·-distribˡ-⊔-≾ = P.·-distribˡ-⊔-≾ ; ·-distribʳ-⊔-≾ = P.·-distribʳ-⊔-≾
  ; ≾-zero-productˡ = P.≾-zero-productˡ ; ≾-zero-productʳ = P.≾-zero-productʳ
  ; ι-zero = ≡⇒≃ P.ι-zero
  ; ι-plus = ≡⇒≃ P.ι-plus
  }
  where
    module P = PosetGrade G
    ≡⇒≃ : ∀ {c d} → c ≡ d → P._≾_ c d × P._≾_ d c
    ≡⇒≃ refl = P.≾-refl , P.≾-refl


-- Morphisms of effect and resource monoids, along a morphism `h` of
-- their durations

record GradeMorphism {D₁ D₂ : Duration} (h : D₁ →ᴰ D₂)
                     (G₁ : Grade D₁) (G₂ : Grade D₂) : Set₁ where
  open Grade G₁ renaming (Carrier to C₁; _≾_ to _≾₁_; 𝟏 to 𝟏₁; _·_ to _·₁_;
                          ⊤ to ⊤₁; _⊔_ to _⊔₁_; ι to ι₁; _≃_ to _≃₁_)
  open Grade G₂ renaming (Carrier to C₂; _≾_ to _≾₂_; 𝟏 to 𝟏₂; _·_ to _·₂_;
                          ⊤ to ⊤₂; _⊔_ to _⊔₂_; ι to ι₂; _≃_ to _≃₂_)

  field

    -- map between carriers of grades
    map    : C₁ → C₂

    -- map is monotone
    map-monotone : {c₁ c₁' : C₁} → (c₁ ≾₁ c₁') → (map c₁ ≾₂ map c₁')

    -- map preserves the monoid structure
    map-𝟏        : map 𝟏₁ ≃₂ 𝟏₂
    map-·        : {c₁ c₁' : C₁} → map (c₁ ·₁ c₁') ≃₂ map c₁ ·₂ map c₁'

    -- map preserves the greatest grade
    map-⊤        : map ⊤₁ ≃₂ ⊤₂

    -- map preserves binary joins
    map-⊔        : {c₁ c₁' : C₁} → map (c₁ ⊔₁ c₁') ≃₂ map c₁ ⊔₂ map c₁'

    -- map preserves the inclusion of durations
    map-ι        : ∀ {τ} → map (ι₁ τ) ≃₂ ι₂ (_→ᴰ_.map h τ)

  -- map preserves the equivalence
  map-≃ : {c₁ c₁' : C₁} → c₁ ≃₁ c₁' → map c₁ ≃₂ map c₁'
  map-≃ a = map-monotone (proj₁ a) , map-monotone (proj₂ a)

-- Morphisms preserving the structure on the nose

record StrictMorphism {D₁ D₂ : Duration} (h : D₁ →ᴰ D₂)
                      (G₁ : Grade D₁) (G₂ : Grade D₂) : Set₁ where
  open Grade G₁ renaming (Carrier to C₁; _≾_ to _≾₁_; 𝟏 to 𝟏₁; _·_ to _·₁_;
                          ⊤ to ⊤₁; _⊔_ to _⊔₁_; ι to ι₁)
  open Grade G₂ renaming (Carrier to C₂; _≾_ to _≾₂_; 𝟏 to 𝟏₂; _·_ to _·₂_;
                          ⊤ to ⊤₂; _⊔_ to _⊔₂_; ι to ι₂)
  field
    map          : C₁ → C₂
    map-monotone : {c₁ c₁' : C₁} → (c₁ ≾₁ c₁') → (map c₁ ≾₂ map c₁')
    map-𝟏        : map 𝟏₁ ≡ 𝟏₂
    map-·        : {c₁ c₁' : C₁} → map (c₁ ·₁ c₁') ≡ (map c₁ ·₂ map c₁')
    map-⊤        : map ⊤₁ ≡ ⊤₂
    map-⊔        : {c₁ c₁' : C₁} → map (c₁ ⊔₁ c₁') ≡ (map c₁ ⊔₂ map c₁')
    map-ι        : ∀ {τ} → map (ι₁ τ) ≡ ι₂ (_→ᴰ_.map h τ)

strictᵍ : {D₁ D₂ : Duration} {h : D₁ →ᴰ D₂} {G₁ : Grade D₁} {G₂ : Grade D₂}
       → StrictMorphism h G₁ G₂ → GradeMorphism h G₁ G₂
strictᵍ {G₂ = G₂} f = record
  { map = map ; map-monotone = map-monotone
  ; map-𝟏 = ≃-reflexive G₂ map-𝟏
  ; map-· = ≃-reflexive G₂ map-·
  ; map-⊤ = ≃-reflexive G₂ map-⊤
  ; map-⊔ = ≃-reflexive G₂ map-⊔
  ; map-ι = ≃-reflexive G₂ map-ι
  }
  where open StrictMorphism f

-- Morphisms of grades over the same durations

_→ᵍ_ : {D : Duration} → Grade D → Grade D → Set₁
G₁ →ᵍ G₂ = GradeMorphism idᴰ G₁ G₂

module _→ᵍ_ {D : Duration} {G₁ G₂ : Grade D} (f : G₁ →ᵍ G₂) =
  GradeMorphism f


-- Grade systems: resource and effect grades over the same durations,
-- and the morphism `∣-∣ᵉ` of effects into resources, `∣ ε ∣ᵉ` the image
-- of `ε`

record GradeSystem : Set₂ where

  field

    Dur    : Duration
    RGrade : Grade Dur
    EGrade : Grade Dur
    ∣-∣ᵉ : EGrade →ᵍ RGrade


-- The fields of the effect and the resource grade, under distinct names

module GradeSystemInterface (GS : GradeSystem) where

  open GradeSystem GS public

  open Duration Dur renaming (Carrier to 𝔻) public

  open Grade RGrade renaming
    (Carrier to R;
     _·_ to _·ᵣ_;
     𝟏 to 𝟏ᵣ;
     _≾_ to _≾ᵣ_;
     _≃_ to _≃ᵣ_;
     ⊤ to ⊤ᵣ;
     _⊔_ to _⊔ᵣ_;
     ι to ιᵣ;
     ·-identityˡ to ·ᵣ-identityˡ;
     ·-identityʳ to ·ᵣ-identityʳ;
     ·-assoc to ·ᵣ-assoc;
     ≾-refl to ≾ᵣ-refl;
     ≾-trans to ≾ᵣ-trans;
     ≾-irrelevant to ≾ᵣ-irrelevant;
     _≾?_ to _≾ᵣ?_;
     ≾-⊤ to ≾-⊤ᵣ;
     ⊔-ubˡ to ⊔ᵣ-ubˡ;
     ⊔-ubʳ to ⊔ᵣ-ubʳ;
     ⊔-lub to ⊔ᵣ-lub;
     ·-monoˡ-≾ to ·ᵣ-monoˡ-≾ᵣ;
     ·-monoʳ-≾ to ·ᵣ-monoʳ-≾ᵣ;
     ·-distribˡ-⊔-≾ to ·ᵣ-distribˡ-⊔ᵣ-≾ᵣ;
     ·-distribʳ-⊔-≾ to ·ᵣ-distribʳ-⊔ᵣ-≾ᵣ;
     ≾-zero-productˡ to ≾ᵣ-zero-productˡ;
     ≾-zero-productʳ to ≾ᵣ-zero-productʳ;
     ι-zero to ιᵣ-zero;
     ι-plus to ιᵣ-plus;
     ≾-reflexive to ≾ᵣ-reflexive;
     ≃-refl to ≃ᵣ-refl;
     ≃-sym to ≃ᵣ-sym;
     ≃-trans to ≃ᵣ-trans;
     ≃-reflexive to ≃ᵣ-reflexive;
     ≃⇒≾ to ≃ᵣ⇒≾ᵣ;
     ≃⇒≿ to ≃ᵣ⇒≿ᵣ;
     ≃-irrelevant to ≃ᵣ-irrelevant;
     _≃?_ to _≃ᵣ?_;
     ·-cong to ·ᵣ-cong;
     ⊔-mono to ⊔ᵣ-mono;
     ⊔-cong to ⊔ᵣ-cong;
     ⊔-idem to ⊔ᵣ-idem;
     ⊔-comm to ⊔ᵣ-comm;
     ⊔-assoc to ⊔ᵣ-assoc;
     ⊔-absorb to ⊔ᵣ-absorb;
     ⊔-⊤ to ⊔ᵣ-⊤ᵣ;
     ·-distribˡ-⊔ to ·ᵣ-distribˡ-⊔ᵣ;
     ·-distribʳ-⊔ to ·ᵣ-distribʳ-⊔ᵣ
    ) public

  open Grade EGrade renaming
    (Carrier to E;
     _·_ to _·ₑ_;
     𝟏 to 𝟏ₑ;
     _≾_ to _≾ₑ_;
     _≃_ to _≃ₑ_;
     ⊤ to ⊤ₑ;
     _⊔_ to _⊔ₑ_;
     ι to ιₑ;
     ·-identityˡ to ·ₑ-identityˡ;
     ·-identityʳ to ·ₑ-identityʳ;
     ·-assoc to ·ₑ-assoc;
     ≾-refl to ≾ₑ-refl;
     ≾-trans to ≾ₑ-trans;
     ≾-irrelevant to ≾ₑ-irrelevant;
     _≾?_ to _≾ₑ?_;
     ≾-⊤ to ≾-⊤ₑ;
     ⊔-ubˡ to ⊔ₑ-ubˡ;
     ⊔-ubʳ to ⊔ₑ-ubʳ;
     ⊔-lub to ⊔ₑ-lub;
     ·-monoˡ-≾ to ·ₑ-monoˡ-≾ₑ;
     ·-monoʳ-≾ to ·ₑ-monoʳ-≾ₑ;
     ·-distribˡ-⊔-≾ to ·ₑ-distribˡ-⊔ₑ-≾ₑ;
     ·-distribʳ-⊔-≾ to ·ₑ-distribʳ-⊔ₑ-≾ₑ;
     ι-zero to ιₑ-zero;
     ι-plus to ιₑ-plus;
     ≾-zero-productˡ to ≾ₑ-zero-productˡ;
     ≾-zero-productʳ to ≾ₑ-zero-productʳ;
     ≾-reflexive to ≾ₑ-reflexive;
     ≃-refl to ≃ₑ-refl;
     ≃-sym to ≃ₑ-sym;
     ≃-trans to ≃ₑ-trans;
     ≃-reflexive to ≃ₑ-reflexive;
     ≃⇒≾ to ≃ₑ⇒≾ₑ;
     ≃⇒≿ to ≃ₑ⇒≿ₑ;
     ≃-irrelevant to ≃ₑ-irrelevant;
     _≃?_ to _≃ₑ?_;
     ·-cong to ·ₑ-cong;
     ⊔-mono to ⊔ₑ-mono;
     ⊔-cong to ⊔ₑ-cong;
     ⊔-idem to ⊔ₑ-idem;
     ⊔-comm to ⊔ₑ-comm;
     ⊔-assoc to ⊔ₑ-assoc;
     ⊔-absorb to ⊔ₑ-absorb;
     ⊔-⊤ to ⊔ₑ-⊤ₑ;
     ·-distribˡ-⊔ to ·ₑ-distribˡ-⊔ₑ;
     ·-distribʳ-⊔ to ·ₑ-distribʳ-⊔ₑ
   ) public

  open _→ᵍ_ ∣-∣ᵉ renaming
    (map to ∣_∣ᵉ;
     map-monotone to map-monotoneᵉ;
     map-𝟏 to map-𝟏ᵉ;
     map-· to map-·ᵉ;
     map-⊤ to map-⊤ᵉ;
     map-⊔ to map-⊔ᵉ;
     map-ι to map-ιᵉ;
     map-≃ to map-≃ᵉ
    ) public
