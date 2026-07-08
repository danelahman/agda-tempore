--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Data.Empty
open import Data.Nat.Base
open import Data.Product hiding (map)
open import Data.Sum hiding (map)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_)

open import Util.Equality

-- Ordered effect and resource monoids

record Grade : Set₁ where
  infixl 7 _·_
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

    -- inclusion of ℕ (d : ℕ → Carrier s.t. ... ? ...)
    of-nat : ℕ → Carrier

    -- including ℕ preserves unit
    of-nat-zero : of-nat 0 ≡ u

    -- including ℕ preserves addition
    of-nat-plus : ∀ {m n} → of-nat (m + n) ≡ of-nat m · of-nat n

    -- ...

  -- _≡_ is included in _≾_
  ≾-reflexive  : _≡_ ⇒ _≾_
  ≾-reflexive refl = ≾-refl

open Grade


-- Morphisms of effect and resource monoids

record _→ᵍ_ (G₁ G₂ : Grade) : Set₁ where
  open Grade G₁ renaming (Carrier to C₁; _≾_ to _≾₁_; u to u₁; _·_ to _·₁_; of-nat to of-nat₁)
  open Grade G₂ renaming (Carrier to C₂; _≾_ to _≾₂_; u to u₂; _·_ to _·₂_; of-nat to of-nat₂)
  
  field

    -- map between carriers of grades
    map    : C₁ → C₂

    -- map is monotone
    map-monotone : {c₁ c₁' : C₁} → (c₁ ≾₁ c₁') → (map c₁ ≾₂ map c₁')

    -- map preserves the monoid structure
    map-u        : map u₁ ≡ u₂
    map-·        : {c₁ c₁' : C₁} → map (c₁ ·₁ c₁') ≡ map c₁ ·₂ map c₁'

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
     ·-monoʳ-≾ to ·ₑ-monoʳ-≾ₑ;
     ·-monoˡ-≾ to ·ₑ-monoˡ-≾ₑ;
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
     map-of-nat to map-of-natᵉ
    ) public
