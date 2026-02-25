--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Data.Empty
open import Data.Nat.Base
open import Data.Product using (Σ-syntax)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_)

open import Util.Equality
open import Util.Ordered.Structures

-- Ordered effect and resource monoids

record Grade : Set₁ where
  infixl 7 _·_

  field

    Carrier : Set₀

    -- monoid operations
    _·_ : Carrier → Carrier → Carrier
    u   : Carrier
    
    -- monoid laws
    ·-identityʳ : (x : Carrier) → (x · u) ≡ x
    ·-identityˡ : (x : Carrier) → (u · x) ≡ x
    ·-assoc     : (x y z : Carrier) → ((x · y) · z) ≡ (x · (y · z))

    -- order on the carrier
    _≾_ : Rel Carrier lzero

    -- unit is the least element
    u≾c  : ∀ {c} → u ≾ c
    c≾u⇒c≡u : ∀ {c} → c ≾ u → c ≡ u
    
    -- _·_ is monotone with respect to _≾_
    ·-monoʳ-≾ : ∀ {c} → _Preserves_⟶_ (c ·_) _≾_ _≾_
    ·-monoˡ-≾ : ∀ {c} → _Preserves_⟶_ (_· c) _≾_ _≾_
 
    -- _≾_ is reflexive and transitive
    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_

    -- _≾_ is irrelevant
    ≾-irrelevant : Irrelevant _≾_

    -- _≾_ and _≡_ (on Carrier) are decidable
    _≾?_ : Decidable _≾_
    _≡?_ : Decidable (_≡_ {A = Carrier})

    -- _≾_ and _≡_ are cancellative
    c·d≾e·d⇒c≾e : ∀ {c d e} → (c · d) ≾ (e · d) → c ≾ e
    d·c≾d·e⇒c≾e : ∀ {c d e} → (d · c) ≾ (d · e) → c ≾ e
    c·d≡e·d⇒c≡e : ∀ {c d e} → (c · d) ≡ (e · d) → c ≡ e
    d·c≡d·e⇒c≡e : ∀ {c d e} → (c · d) ≡ (e · d) → c ≡ e

    -- non-zero-divisor property of _·_
    c·d≡u⇒c≡u : ∀ {c d} → c · d ≡ u → c ≡ u
    c·d≡u⇒d≡u : ∀ {c d} → c · d ≡ u → d ≡ u

    -- inclusion of ℕ (d : ℕ → Carrier s.t. ... ? ...)
    embedNat : ℕ → Carrier

    -- ...

  -- helpful axiliary lemma: _≡_ is included in _≾_
  ≾-reflexive  : _≡_ ⇒ _≾_
  ≾-reflexive refl = ≾-refl

open Grade


-- Morphisms of effect and resource monoids

record _→ᵍ_ (G G' : Grade) : Set₁ where

  field

    map : Carrier G → Carrier G'

    -- laws


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
     u≾c to uᵣ≾ᵣc;
     ≾-irrelevant to ≾ᵣ-irrelevant;
     _≾?_ to _≾ᵣ?_;
     _≡?_ to _≡ᵣ?_;
     c·d≡u⇒c≡u to c·ᵣd≡uᵣ⇒c≡uᵣ;
     c·d≡u⇒d≡u to c·ᵣd≡uᵣ⇒d≡uᵣ;
     c≾u⇒c≡u to c≾ᵣuᵣ⇒c≡uᵣ;
     c·d≾e·d⇒c≾e to c·ᵣd≾ᵣe·d⇒c≾ᵣe;
     c·d≡e·d⇒c≡e to c·ᵣd≡e·ᵣd⇒c≡e;
     embedNat to embedR;
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
     _≾?_ to _≾ₑ?_;
     _≡?_ to _≡ₑ?_;
     embedNat to embedE;
     ≾-reflexive to ≾ₑ-reflexive
   ) public

  open _→ᵍ_ ∣_∣ᵉ renaming (map to mapᵉ) public

