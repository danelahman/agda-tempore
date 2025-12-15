--------------------------------------
-- Grades for effects and resources --
--------------------------------------

module Syntax.Grades where

open import Level
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
    _≈_ : Rel Carrier zero
    _·_ : Carrier → Carrier → Carrier
    u   : Carrier

    -- order
    _≾_ : Rel Carrier zero

    -- monoid is ordered
    isCommutativePomonoid : IsCommutativePomonoid _≈_ _≾_ _·_ u
    
    -- u is the neutral of the _·_ operation (right)
    ·-identityʳ : (x : Carrier) → (x · u) ≡ x

    -- u is the neutral of the _·_ operation (left)
    ·-identityˡ : (x : Carrier) → (u · x) ≡ x

    -- u is the least element in Carrier
    u≾c : ∀ {c} → u ≾ c

    -- _·_ is associative
    ·-assoc : (x y z : Carrier) → ((x · y) · z) ≡ (x · (y · z))

    -- _·_ is commutative
    ·-comm : (x y : Carrier) → (x · y) ≡ (y · x)

    -- _·_ is monotone w.r.t. _≾_ (right)
    ·-monoʳ-≾ : (c : Carrier) → _Preserves_⟶_ (c ·_) _≾_ _≾_

    -- _·_ is monotone w.r.t. _≾_ (left)
    ·-monoˡ-≾ : (c : Carrier) → _Preserves_⟶_ (_· c) _≾_ _≾_

-- _≾_ is reflexive and transitive
    ≾-reflexive  : _≡_ ⇒ _≾_

    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_
   
    -- inclusion of ℕ (d : ℕ → Carrier s.t. ... ? ...)

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
    ∣_∣ʳ : RGrade →ᵍ EGrade


module GradeSystemInterface (GS : GradeSystem) where

  open GradeSystem GS public

  open Grade RGrade renaming
    (Carrier to R;
     _·_ to _·ᵣ_;
     u to uᵣ;
     ·-identityʳ to ·-identityʳᵣ;
     ·-assoc to ·-assocᵣ;
     _≾_ to _≾ᵣ_;
     ·-monoʳ-≾ to ·-monoʳ-≾ᵣ;
     ·-comm to ·-commᵣ;
     ≾-reflexive to ≾-reflexiveᵣ;
     ≾-trans to ≾-transᵣ
    ) public


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
