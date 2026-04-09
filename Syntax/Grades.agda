--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Algebra.Definitions

open import Data.Empty
open import Data.Nat.Base
open import Data.Product hiding (map)
open import Data.Sum hiding (map)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary using (¬_)

open import Util.Equality
open import Util.Ordered.Structures

-- Ordered effect and resource monoids

record Grade : Set₁ where
  infixl 7 _·_
  infixl 5 _≾_

  field

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

    -- u is minimal
    u-minimal : ∀ {c} → c ≾ u → c ≡ u
    
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

    -- _≡_ is cancellative
    ·-≡-cancellative : ∀ {c d e f g} → c · e · d ≡ f · e · g → c · d ≡ f · g

    -- _≾_ is right cancellative
    ·-≾-cancelʳ : RightCancellative _≾_ _·_

    -- _·_ and u have zero-product property
    ·-zero-productˡ : ∀ {c d} → c · d ≡ u → c ≡ u
    ·-zero-productʳ : ∀ {c d} → c · d ≡ u → d ≡ u

    -- inclusion of ℕ (d : ℕ → Carrier s.t. ... ? ...)
    embedNat : ℕ → Carrier

    -- ...

  -- _≡_ is included in _≾_
  ≾-reflexive  : _≡_ ⇒ _≾_
  ≾-reflexive refl = ≾-refl

  -- binary cancellation lemmas  
  ·-cancellativeˡ : ∀ {c d e} → c · d ≡ e · d → c ≡ e
  ·-cancellativeˡ {c} {d} {e} p =
    begin
      c
      ≡⟨ sym (·-identityʳ c) ⟩
      c · u
      ≡⟨ ·-≡-cancellative (trans (·-identityʳ (c · d)) (trans p (sym (·-identityʳ (e · d))))) ⟩
      e · u
      ≡⟨ ·-identityʳ e ⟩
      e
    ∎

  ·-cancellativeʳ : ∀ {c d e} → d · c ≡ d · e → c ≡ e
  ·-cancellativeʳ {c} {d} {e} p =
    begin
      c
    ≡⟨ sym (·-identityˡ c) ⟩
      u · c
    ≡⟨ ·-≡-cancellative
         (trans (trans (·-assoc u d c) (·-identityˡ (d · c)))
         (trans p (trans (sym (·-identityˡ (d · e))) (sym (·-assoc u d e))))) ⟩
      u · e
    ≡⟨ ·-identityˡ e ⟩
      e
    ∎
  
  -- contrapositive version of the zero-product property of _·_
  ·-zero-productˡ-≢ : ∀ {c d} → c ≢ u → c · d ≢ u
  ·-zero-productˡ-≢ p q = p (·-zero-productˡ q)
  
  ·-zero-productʳ-≢ : ∀ {c d} → d ≢ u → c · d ≢ u
  ·-zero-productʳ-≢ p q = p (·-zero-productʳ q)

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
     ≾-irrelevant to ≾ᵣ-irrelevant;
     _≾?_ to _≾ᵣ?_;
     _≡?_ to _≡ᵣ?_;
     ·-≡-cancellative to ·ᵣ-≡-cancellative;
     ·-≾-cancelʳ to ·ᵣ-≾ᵣ-cancelʳ;
     ·-zero-productˡ to ·ᵣ-zero-productˡ;
     ·-zero-productʳ to ·ᵣ-zero-productʳ;
     u-minimal to uᵣ-minimal;
     embedNat to embedR;
     ≾-reflexive to ≾ᵣ-reflexive;
     ·-cancellativeˡ to ·ᵣ-cancellativeˡ;
     ·-cancellativeʳ to ·ᵣ-cancellativeʳ;     
     ·-zero-productˡ-≢ to ·ᵣ-zero-productˡ-≢;
     ·-zero-productʳ-≢ to ·ᵣ-zero-productʳ-≢
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
     ·-≡-cancellative to ·ₑ-≡-cancellative;
     embedNat to embedE;
     ≾-reflexive to ≾ₑ-reflexive;
     ·-cancellativeˡ to ·ₑ-cancellativeˡ;
     ·-cancellativeʳ to ·ₑ-cancellativeʳ;     
     ·-zero-productˡ-≢ to ·ₑ-zero-productˡ-≢;
     ·-zero-productʳ-≢ to ·ₑ-zero-productʳ-≢
   ) public

  open _→ᵍ_ ∣_∣ᵉ renaming (map to mapᵉ) public

