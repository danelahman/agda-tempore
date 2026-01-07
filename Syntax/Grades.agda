--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Data.Nat.Base

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions

open import Util.Equality
open import Util.Ordered.Structures

record Grade : Set₁ where
  infixl 7 _·_
  infix  4 _≈_

  field

    Carrier : Set₀

    -- monoid ops
    _≈_ : Rel Carrier lzero
    _·_ : Carrier → Carrier → Carrier
    u   : Carrier

    -- order
    _≾_ : Rel Carrier lzero

    -- monoid is ordered
    isPomonoid : IsPomonoid _≈_ _≾_ _·_ u
    
    -- u is the neutral of the _·_ operation (right)
    ·-identityʳ : (x : Carrier) → (x · u) ≡ x

    -- u is the neutral of the _·_ operation (left)
    ·-identityˡ : (x : Carrier) → (u · x) ≡ x

    -- u is the least element in Carrier
    u≾c : ∀ {c} → u ≾ c

    -- _·_ is associative
    ·-assoc : (x y z : Carrier) → ((x · y) · z) ≡ (x · (y · z))

    -- _·_ is monotone w.r.t. _≾_ (right)
    ·-monoʳ-≾ : (c : Carrier) → _Preserves_⟶_ (c ·_) _≾_ _≾_

    -- _·_ is monotone w.r.t. _≾_ (left)
    ·-monoˡ-≾ : (c : Carrier) → _Preserves_⟶_ (_· c) _≾_ _≾_
 
    -- _≾_ is reflexive and transitive
    ≾-reflexive  : _≡_ ⇒ _≾_

    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_

    -- _≾_ is irrelevant
    ≾-irrelevant : Irrelevant _≾_

    -- _≾_ is decidable
    _≾?_ : Decidable _≾_

    -- Properties of _·_ and _≾_
    c≾c·d : (c d : Carrier) → c ≾ (c · d)

    c≾d⇒c≾d·b : ∀ {c d} b → c ≾ d → c ≾ (d · b)

    γ-≾-substₗ : ∀ {γ γ' γ''} → γ' ≡ γ'' → γ' ≾ γ → γ'' ≾ γ
    
    γ-≾-substᵣ : ∀ {γ γ' γ''} → γ' ≡ γ'' → γ ≾ γ'' → γ ≾ γ'

    -- inclusion of ℕ (d : ℕ → Carrier s.t. ... ? ...)
    embedNat : ℕ → Carrier

    -- ...


open Grade



record _→ᵍ_ (G G' : Grade) : Set₁ where

  field

    map : Carrier G → Carrier G'

    -- laws



record GradeSystem : Set₂ where

  field

    RGrade : Grade
    EGrade : Grade
    ∣_∣ᵉ : EGrade →ᵍ RGrade
    ∣_∣ʳ : RGrade →ᵍ EGrade -- remove?


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
     ≾-reflexive to ≾ᵣ-reflexive;
     ≾-trans to ≾ᵣ-trans;
     ≾-refl to ≾ᵣ-refl;
     u≾c to uᵣ≾ᵣc;
     ≾-irrelevant to ≾ᵣ-irrelevant;
     c≾c·d to c≾ᵣc·ᵣd;
     γ-≾-substₗ to ρ-≾ᵣ-substₗ;
     γ-≾-substᵣ to ρ-≾ᵣ-substᵣ;
     c≾d⇒c≾d·b to c≾ᵣd⇒c≾ᵣd·ᵣb;
     embedNat to embedR;
     _≾?_ to _≾ᵣ?_
    ) public

  open Grade EGrade renaming
    (Carrier to E;
     _·_ to _·ₑ_;
     u to uₑ;
     ·-identityʳ to ·ₑ-identityʳ;
     ·-assoc to ·ₑ-assoc;
     _≾_ to _≾ₑ_;
     ·-monoʳ-≾ to ·ₑ-monoʳ-≾ₑ;
     ≾-reflexive to ≾ₑ-reflexive;
     ≾-trans to ≾ₑ-trans;
     embedNat to embedE;
     _≾?_ to _≾ₑ?_
   ) public

  open _→ᵍ_ ∣_∣ᵉ renaming (map to mapᵉ) public


{-
module Syntax.Grades
  {cₑ ℓ₁ ℓ₂} {E : Set cₑ} -- The underlying set (effects)
  {cᵣ ℓ₃ ℓ₄} {R : Set cᵣ} -- The underlying set (resources)
  {cpomₑ : CommutativePomonoid cₑ ℓ₁ ℓ₂}
  {cpomᵣ : CommutativePomonoid cᵣ ℓ₃ ℓ₄}
  where

open import Relation.Binary
open import Util.Ordered.Structures
open import Agda.Primitive
open import Algebra.Core

-- Grades for effects
Timeₑ : Set cₑ
Timeₑ = Carrierₑ
  where open CommutativePomonoid cpomₑ renaming (Carrier to Carrierₑ)
  
-- Grades for resources
Timeᵣ : Set cᵣ
Timeᵣ = Carrierᵣ
  where open CommutativePomonoid cpomᵣ renaming (Carrier to Carrierᵣ)

-- Old version:
-- Timeᵣ : Set (lsuc (cᵣ ⊔ ℓ₃ ⊔ ℓ₄))
-- Timeᵣ = CommutativePomonoid cᵣ ℓ₃ ℓ₄
-}
