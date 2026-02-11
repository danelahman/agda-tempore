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
    _≺_ : Rel Carrier lzero

    -- monoid is ordered
    isPomonoid : IsPomonoid _≈_ _≾_ _·_ u
    
    -- u is the neutral of the _·_ operation (right)
    ·-identityʳ : (x : Carrier) → (x · u) ≡ x

    -- u is the neutral of the _·_ operation (left)
    ·-identityˡ : (x : Carrier) → (u · x) ≡ x

    -- u is the least element in Carrier
    u≾c : ∀ {c} → u ≾ c
    c≺u-contradiction : ∀ {c} → (c ≺ u) → ⊥

    --
    c≺d→d≾c-contradiction : ∀ {c d} → c ≺ d → d ≾ c → ⊥

    -- _·_ is associative
    ·-assoc : (x y z : Carrier) → ((x · y) · z) ≡ (x · (y · z))

    -- _·_ is monotone w.r.t. _≾_ and _≺_ (right)
    ·-monoʳ-≾ : (c : Carrier) → _Preserves_⟶_ (c ·_) _≾_ _≾_
    ·-monoʳ-≺ : (c : Carrier) → _Preserves_⟶_ (c ·_) _≺_ _≺_

    -- _·_ is monotone w.r.t. _≾_ (left)
    ·-monoˡ-≾ : (c : Carrier) → _Preserves_⟶_ (_· c) _≾_ _≾_
 
    -- _≾_ is reflexive and transitive
    ≾-reflexive  : _≡_ ⇒ _≾_

    ≾-refl  : Reflexive _≾_
    ≾-trans : Transitive _≾_
    ≺-trans : Transitive _≺_

    -- _≾_ is irrelevant
    ≾-irrelevant : Irrelevant _≾_

    -- _≾_ and _≈_ and _≺_ are decidable
    _≾?_ : Decidable _≾_
    _≈?_ : Decidable _≈_
    _≺?_ : Decidable _≺_

-- relation between ≾ and ≺
    ¬≾⇒≻flip : ∀ {a b} → ¬ (a ≾ b) → (b ≺ a)
    ¬≺⇒≿flip : ∀ {a b} → ¬ (a ≺ b) → (b ≾ a)

    --
    c≾u⇒c≡u : (c : Carrier) → c ≾ u → c ≡ u

    c≉u⇒u≺c : ∀ {c} → ¬ (c ≈ u) → u ≺ c

    c≈d⇒c≡d : ∀ {c d} → c ≈ d → c ≡ d

   
    -- Properties of _·_ and _≾_ and _≺_
    
    c≾c·d : ∀ {c d} → c ≾ (c · d)
--    c·d≾c : (c d : Carrier) → (c · d) ≾ c

--    c≾d⇒c≾d·b : ∀ {c d} b → c ≾ d → c ≾ (d · b)
--    c≾d⇒c·b≾d : ∀ {c d} b → c ≾ d → (c · b) ≾ d

    c·d≾e·d⇒c≾e : ∀ {c d e} → (c · d) ≾ (e · d) → c ≾ e
    c·d≺e·d⇒c≺e : ∀ {c d e} → (c · d) ≺ (e · d) → c ≺ e

    γ-≾-substₗ : ∀ {γ γ' γ''} → γ' ≡ γ'' → γ' ≾ γ → γ'' ≾ γ
    
    γ-≾-substᵣ : ∀ {γ γ' γ''} → γ' ≡ γ'' → γ ≾ γ'' → γ ≾ γ'

    u≺c⇒u≢c : ∀ {c} → u ≺ c → ¬ (u ≡ c)

    -- Properties of _·_ and _≡_
    c·d≡u⇒c≡u : ∀ {d} → (c : Carrier) → c · d ≡ u → c ≡ u

    c·d≡u⇒d≡u : ∀ {c} → (d : Carrier) → c · d ≡ u → d ≡ u

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
     _≈_ to _≈ᵣ_;
     _≾_ to _≾ᵣ_;
     _≺_ to _≺ᵣ_;
     ·-monoʳ-≾ to ·ᵣ-monoʳ-≾ᵣ;
     ·-monoʳ-≺ to ·ᵣ-monoʳ-≺ᵣ;
     ·-monoˡ-≾ to ·ᵣ-monoˡ-≾ᵣ;
     ≾-reflexive to ≾ᵣ-reflexive;
     ≾-trans to ≾ᵣ-trans;
     ≾-refl to ≾ᵣ-refl;
     u≾c to uᵣ≾ᵣc;
     c≈d⇒c≡d to c≈ᵣd⇒c≡d;
     ≾-irrelevant to ≾ᵣ-irrelevant;
     c≾c·d to c≾ᵣc·ᵣd;
--     c·d≾c to c·ᵣd≾ᵣc;
     γ-≾-substₗ to ρ-≾ᵣ-substₗ;
     γ-≾-substᵣ to ρ-≾ᵣ-substᵣ;
--     c≾d⇒c≾d·b to c≾ᵣd⇒c≾ᵣd·ᵣb;
--     c≾d⇒c·b≾d to c≾ᵣd⇒c·ᵣb≾ᵣd;
     embedNat to embedR;
     _≾?_ to _≾ᵣ?_;
     _≈?_ to _≈ᵣ?_; 
     _≺?_ to _≺ᵣ?_;
     c·d≡u⇒c≡u to c·ᵣd≡uᵣ⇒c≡uᵣ;
     c·d≡u⇒d≡u to c·ᵣd≡uᵣ⇒d≡uᵣ;
     c≾u⇒c≡u to c≾ᵣuᵣ⇒c≡uᵣ;
     ¬≾⇒≻flip to ¬≾ᵣ⇒≻ᵣflip;
     ¬≺⇒≿flip to ¬≺ᵣ⇒≿ᵣflip;
     ≺-trans to ≺ᵣ-trans;
     c·d≾e·d⇒c≾e to c·ᵣd≾ᵣe·d⇒c≾ᵣe;
     c≺u-contradiction to c≺ᵣuᵣ-contradiction;
     c≉u⇒u≺c to c≉ᵣuᵣ⇒uᵣ≺ᵣc;
     c≺d→d≾c-contradiction to c≺ᵣd→d≾ᵣc-contradiction;
     c·d≺e·d⇒c≺e to c·ᵣd≺ᵣe·ᵣd⇒c≺ᵣe;
     u≺c⇒u≢c to uᵣ≺ᵣc⇒uᵣ≢c
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
