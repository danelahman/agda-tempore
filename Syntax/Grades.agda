--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Data.Empty
open import Data.Nat.Base hiding (_⊔_)
open import Data.Product hiding (map)
open import Data.Sum hiding (map)

open import Level hiding (_⊔_) renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_)

open import Util.Equality

-- Ordered effect and resource monoids

record Grade : Set₁ where
  infixl 7 _·_
  infixl 6 _⊔_
  infixl 5 _≾_

  field

    -- carrier type of grades
    Carrier : Set₀

    -- monoid operations
    _·_ : Carrier → Carrier → Carrier
    u   : Carrier
    
    -- monoid laws
    ·-identityʳ : (c : Carrier) → (c · u) ≡ c
    ·-identityˡ : (c : Carrier) → (u · c) ≡ c
    ·-assoc     : (c d e : Carrier) → (c · d) · e ≡ c · (d · e)

    -- order
    _≾_ : Rel Carrier lzero

    -- the designated greatest grade
    ⊤ : Carrier

    -- every grade may be weakened to ⊤
    ≾-⊤ : (c : Carrier) → c ≾ ⊤

    -- binary joins
    _⊔_          : Carrier → Carrier → Carrier
    ⊔-ubˡ        : (c d : Carrier) → c ≾ c ⊔ d
    ⊔-ubʳ        : (c d : Carrier) → d ≾ c ⊔ d
    ⊔-lub        : {c d e : Carrier} → c ≾ e → d ≾ e → c ⊔ d ≾ e

    -- `_·_` distributes over `_⊔_`, in the direction monotonicity does
    -- not already give
    ·-distribˡ-⊔ : (c d e : Carrier) → c · (d ⊔ e) ≾ (c · d) ⊔ (c · e)
    ·-distribʳ-⊔ : (c d e : Carrier) → (d ⊔ e) · c ≾ (d · c) ⊔ (e · c)

    -- _·_ is monotone with respect to _≾_
    ·-monoˡ-≾ : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
    ·-monoʳ-≾ : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_
 
    -- _≾_ is reflexive and transitive
    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_

    -- _≾_ is proof irrelevant
    ≾-irrelevant : ∀ {c d} → (p q : c ≾ d) → p ≡ q

    -- _≡_ (on Carrier) is decidable
    _≡?_ : Decidable (_≡_ {A = Carrier})

    -- _≾_ and u have zero-product property
    ≾-zero-productˡ : ∀ {c d} → c · d ≾ u → c ≾ u
    ≾-zero-productʳ : ∀ {c d} → c · d ≾ u → d ≾ u

    -- inclusion of ℕ, mapping `n` to the grade of `n` time steps
    of-nat : ℕ → Carrier

    -- including ℕ preserves unit
    of-nat-zero : of-nat 0 ≡ u

    -- including ℕ preserves addition
    of-nat-plus : ∀ {m n} → of-nat (m + n) ≡ of-nat m · of-nat n

  -- _≡_ is included in _≾_
  ≾-reflexive  : _≡_ ⇒ _≾_
  ≾-reflexive refl = ≾-refl

  -- _⊔_ is monotone with respect to _≾_
  ⊔-mono : ∀ {c c' d d'} → c ≾ c' → d ≾ d' → c ⊔ d ≾ c' ⊔ d'
  ⊔-mono {c' = c'} {d' = d'} p q =
    ⊔-lub (≾-trans p (⊔-ubˡ c' d')) (≾-trans q (⊔-ubʳ c' d'))

  -- _⊔_ is idempotent, commutative and associative up to _≾_
  ⊔-idem-≾ : (c : Carrier) → c ⊔ c ≾ c
  ⊔-idem-≾ c = ⊔-lub ≾-refl ≾-refl

  ⊔-comm-≾ : (c d : Carrier) → c ⊔ d ≾ d ⊔ c
  ⊔-comm-≾ c d = ⊔-lub (⊔-ubʳ d c) (⊔-ubˡ d c)

  ⊔-assoc-≾ : (c d e : Carrier) → (c ⊔ d) ⊔ e ≾ c ⊔ (d ⊔ e)
  ⊔-assoc-≾ c d e =
    ⊔-lub (⊔-lub (⊔-ubˡ c (d ⊔ e))
                 (≾-trans (⊔-ubˡ d e) (⊔-ubʳ c (d ⊔ e))))
          (≾-trans (⊔-ubʳ d e) (⊔-ubʳ c (d ⊔ e)))

  -- ⊤ absorbs joins; the converse is `⊔-ubʳ`, so the two together say
  -- that `c ⊔ ⊤` and `⊤` are equivalent
  ⊔-⊤ : (c : Carrier) → c ⊔ ⊤ ≾ ⊤
  ⊔-⊤ c = ⊔-lub (≾-⊤ c) ≾-refl

  -- the converses of `·-distribˡ-⊔` and `·-distribʳ-⊔`, which follow
  -- from `_·_` being monotone in each argument separately
  ·-distribˡ-⊔⁻¹ : (c d e : Carrier) → (c · d) ⊔ (c · e) ≾ c · (d ⊔ e)
  ·-distribˡ-⊔⁻¹ c d e =
    ⊔-lub (·-monoʳ-≾ (⊔-ubˡ d e)) (·-monoʳ-≾ (⊔-ubʳ d e))

  ·-distribʳ-⊔⁻¹ : (c d e : Carrier) → (d · c) ⊔ (e · c) ≾ (d ⊔ e) · c
  ·-distribʳ-⊔⁻¹ c d e =
    ⊔-lub (·-monoˡ-≾ (⊔-ubˡ d e)) (·-monoˡ-≾ (⊔-ubʳ d e))

open Grade


-- Morphisms of effect and resource monoids

record _→ᵍ_ (G₁ G₂ : Grade) : Set₁ where
  open Grade G₁ renaming (Carrier to C₁; _≾_ to _≾₁_; u to u₁; _·_ to _·₁_;
                          ⊤ to ⊤₁; _⊔_ to _⊔₁_; of-nat to of-nat₁)
  open Grade G₂ renaming (Carrier to C₂; _≾_ to _≾₂_; u to u₂; _·_ to _·₂_;
                          ⊤ to ⊤₂; _⊔_ to _⊔₂_; of-nat to of-nat₂)
  
  field

    -- map between carriers of grades
    map    : C₁ → C₂

    -- map is monotone
    map-monotone : {c₁ c₁' : C₁} → (c₁ ≾₁ c₁') → (map c₁ ≾₂ map c₁')

    -- map preserves the monoid structure
    map-u        : map u₁ ≡ u₂
    map-·        : {c₁ c₁' : C₁} → map (c₁ ·₁ c₁') ≡ map c₁ ·₂ map c₁'

    -- map preserves the greatest grade
    map-⊤        : map ⊤₁ ≡ ⊤₂

    -- map preserves binary joins
    map-⊔        : {c₁ c₁' : C₁} → map (c₁ ⊔₁ c₁') ≡ map c₁ ⊔₂ map c₁'

    -- map preserves inclusion of ℕ
    map-of-nat   : ∀ {n} → map (of-nat₁ n) ≡ of-nat₂ n


-- Grade systems

record GradeSystem : Set₂ where

  field

    RGrade : Grade
    EGrade : Grade
    ∣_∣ᵉ : EGrade →ᵍ RGrade


-- Helpful module exporting effect and resource grade fields with different names

module GradeSystemInterface (GS : GradeSystem) where

  open GradeSystem GS public

  open Grade RGrade renaming
    (Carrier to R;
     _·_ to _·ᵣ_;
     u to uᵣ;
     ·-identityʳ to ·ᵣ-identityʳ;
     ·-identityˡ to ·ᵣ-identityˡ;
     ·-assoc to ·ᵣ-assoc;
     _≾_ to _≾ᵣ_;
     ⊤ to ⊤ᵣ;
     ≾-⊤ to ≾-⊤ᵣ;
     _⊔_ to _⊔ᵣ_;
     ⊔-ubˡ to ⊔ᵣ-ubˡ;
     ⊔-ubʳ to ⊔ᵣ-ubʳ;
     ⊔-lub to ⊔ᵣ-lub;
     ⊔-mono to ⊔ᵣ-mono;
     ⊔-idem-≾ to ⊔ᵣ-idem-≾ᵣ;
     ⊔-comm-≾ to ⊔ᵣ-comm-≾ᵣ;
     ⊔-assoc-≾ to ⊔ᵣ-assoc-≾ᵣ;
     ⊔-⊤ to ⊔ᵣ-⊤ᵣ;
     ·-distribˡ-⊔ to ·ᵣ-distribˡ-⊔ᵣ;
     ·-distribʳ-⊔ to ·ᵣ-distribʳ-⊔ᵣ;
     ·-distribˡ-⊔⁻¹ to ·ᵣ-distribˡ-⊔ᵣ⁻¹;
     ·-distribʳ-⊔⁻¹ to ·ᵣ-distribʳ-⊔ᵣ⁻¹;
     ·-monoʳ-≾ to ·ᵣ-monoʳ-≾ᵣ;
     ·-monoˡ-≾ to ·ᵣ-monoˡ-≾ᵣ;
     ≾-refl to ≾ᵣ-refl;
     ≾-trans to ≾ᵣ-trans;
     ≾-irrelevant to ≾ᵣ-irrelevant;
     _≡?_ to _≡ᵣ?_;
     ≾-zero-productˡ to ≾ᵣ-zero-productˡ;
     ≾-zero-productʳ to ≾ᵣ-zero-productʳ;
     of-nat to of-natʳ;
     of-nat-zero to of-natʳ-zero;
     of-nat-plus to of-natʳ-plus;
     ≾-reflexive to ≾ᵣ-reflexive
    ) public

  open Grade EGrade renaming
    (Carrier to E;
     _·_ to _·ₑ_;
     u to uₑ;
     ·-identityʳ to ·ₑ-identityʳ;
     ·-identityˡ to ·ₑ-identityˡ;
     ·-assoc to ·ₑ-assoc;
     _≾_ to _≾ₑ_;
     ⊤ to ⊤ₑ;
     ≾-⊤ to ≾-⊤ₑ;
     _⊔_ to _⊔ₑ_;
     ⊔-ubˡ to ⊔ₑ-ubˡ;
     ⊔-ubʳ to ⊔ₑ-ubʳ;
     ⊔-lub to ⊔ₑ-lub;
     ⊔-mono to ⊔ₑ-mono;
     ⊔-idem-≾ to ⊔ₑ-idem-≾ₑ;
     ⊔-comm-≾ to ⊔ₑ-comm-≾ₑ;
     ⊔-assoc-≾ to ⊔ₑ-assoc-≾ₑ;
     ⊔-⊤ to ⊔ₑ-⊤ₑ;
     ·-distribˡ-⊔ to ·ₑ-distribˡ-⊔ₑ;
     ·-distribʳ-⊔ to ·ₑ-distribʳ-⊔ₑ;
     ·-distribˡ-⊔⁻¹ to ·ₑ-distribˡ-⊔ₑ⁻¹;
     ·-distribʳ-⊔⁻¹ to ·ₑ-distribʳ-⊔ₑ⁻¹;
     ·-monoʳ-≾ to ·ₑ-monoʳ-≾ₑ;
     ·-monoˡ-≾ to ·ₑ-monoˡ-≾ₑ;
     ≾-refl to ≾ₑ-refl;
     ≾-trans to ≾ₑ-trans;
     ≾-irrelevant to ≾ₑ-irrelevant;
     _≡?_ to _≡ₑ?_;
     of-nat to of-natᵉ;
     of-nat-zero to of-natᵉ-zero;
     of-nat-plus to of-natᵉ-plus;
     ≾-reflexive to ≾ₑ-reflexive
   ) public

  open _→ᵍ_ ∣_∣ᵉ renaming
    (map to mapᵉ;
     map-monotone to map-monotoneᵉ;
     map-u to map-uᵉ;
     map-· to map-·ᵉ;
     map-⊤ to map-⊤ᵉ;
     map-⊔ to map-⊔ᵉ;
     map-of-nat to map-of-natᵉ
    ) public
