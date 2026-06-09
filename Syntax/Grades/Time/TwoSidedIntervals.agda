--------------------------------------------
-- Two-sided (closed) intervals as grades --
--------------------------------------------

module Syntax.Grades.Time.TwoSidedIntervals where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Syntax.Grades

open import Util.Equality

-- type of intervals

record Interval : Set₀ where
  constructor [_,_]tsi
  field
    min : ℕ
    max : ℕ
    -- min is smaller or equal than max
    min≤max : min ≤ max

open Interval public

-- interval addition

_·ᵢ_ : Interval → Interval → Interval
i₁ ·ᵢ i₂ = [ min i₁ + min i₂ , max i₁ + max i₂ ]tsi (+-mono-≤ (min≤max i₁) (min≤max i₂))

infixl 7 _·ᵢ_

-- interval equality

eqᵢ : ∀ {i₁ i₂}
    → min i₁ ≡ min i₂
    → max i₁ ≡ max i₂
    -----------------
    → i₁ ≡ i₂

eqᵢ {_} {i₂} refl refl = cong (λ x → [ min i₂ , max i₂ ]tsi x) (≤-irrelevant _ _)

-- right and left identity

·ᵢ-identityʳ : (i : Interval) → (i ·ᵢ [ 0 , 0 ]tsi z≤n) ≡ i
·ᵢ-identityʳ i =
  eqᵢ (+-identityʳ (min i)) (+-identityʳ (max i))

·ᵢ-identityˡ : (i : Interval) → ([ 0 , 0 ]tsi z≤n ·ᵢ i) ≡ i
·ᵢ-identityˡ i =
  eqᵢ (+-identityˡ (min i)) (+-identityˡ (max i))

-- _·ᵢ_ is associative

·ᵢ-assoc : (i₁ i₂ i₃ : Interval) → (i₁ ·ᵢ i₂) ·ᵢ i₃ ≡ i₁ ·ᵢ (i₂ ·ᵢ i₃)
·ᵢ-assoc i₁ i₂ i₃ =
  eqᵢ
    (+-assoc (min i₁) (min i₂) (min i₃))
    (+-assoc (max i₁) (max i₂) (max i₃))

-- interval order

_≾ᵢ_ : Rel Interval lzero
i₁ ≾ᵢ i₂ =
  (min i₂ ≤ min i₁ × max i₁ ≤ max i₂)

-- [ 0 , 0 ]tsi is the minimal element

[0,0]tsi-minimal : ∀ {i} → i ≾ᵢ [ 0 , 0 ]tsi z≤n → i ≡ [ 0 , 0 ]tsi z≤n
[0,0]tsi-minimal {i} (minrel , maxrel) =
  eqᵢ {i} {[ 0 , 0 ]tsi z≤n} (n≤0⇒n≡0 (≤-trans (min≤max i) maxrel)) (n≤0⇒n≡0 maxrel)

-- monotonicity

·ᵢ-monoʳ-≾ᵢ : ∀ {i} → _·ᵢ_ i Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoʳ-≤ (min i) {min i₂} {min i₁} minrel , 
  +-monoʳ-≤ (max i) {max i₁} {max i₂} maxrel

·ᵢ-monoˡ-≾ᵢ : ∀ {i} → (_·ᵢ i) Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoˡ-≤ (min i) {min i₂} {min i₁} minrel ,
  +-monoˡ-≤ (max i) {max i₁} {max i₂} maxrel

-- irrelevance

≾ᵢ-irrelevant : Irrelevant _≾ᵢ_
≾ᵢ-irrelevant (relmin , relmax) (predmin , predmax) =
  cong₂ _,_ (≤-irrelevant relmin predmin) (≤-irrelevant relmax predmax)

-- decidability

eqᵢ? : Decidable {lzero} {Interval} _≡_
eqᵢ? i₁ i₂ with min i₁ ≟ min i₂ | max i₁ ≟ max i₂
... | yes p | yes q = yes (eqᵢ p q)
... | yes _ | no ¬q = no  λ x → ¬q (cong max x)
... | no ¬p | _     = no  λ x → ¬p (cong min x)

-- cancellativity

·ᵢ-≾ᵢ-cancellativeˡ : (i₁ i₂ i₃ : Interval) → (i₁ ·ᵢ i₂) ≾ᵢ (i₁ ·ᵢ i₃) → i₂ ≾ᵢ i₃
·ᵢ-≾ᵢ-cancellativeˡ i₁ i₂ i₃ rel =
  +-cancelˡ-≤ (min i₁) (min i₃) (min i₂) (proj₁ rel) ,
  +-cancelˡ-≤ (max i₁) (max i₂) (max i₃) (proj₂ rel)

-- zero-product property

≡ᵢ-zero-productˡ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ [ 0 , 0 ]tsi z≤n → i₁ ≡ [ 0 , 0 ]tsi z≤n
≡ᵢ-zero-productˡ {i₁} {_} eq =
   eqᵢ
     (m+n≡0⇒m≡0 (min i₁) (cong min eq))
     (m+n≡0⇒m≡0 (max i₁) (cong max eq))

≡ᵢ-zero-productʳ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ [ 0 , 0 ]tsi z≤n → i₂ ≡ [ 0 , 0 ]tsi z≤n
≡ᵢ-zero-productʳ {i₁} {i₂} eq =
  eqᵢ
    (m+n≡0⇒n≡0 (min i₁) {min i₂} (cong min eq))
    (m+n≡0⇒n≡0 (max i₁) {max i₂} (cong max eq))

≾ᵢ-zero-productˡ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ [ 0 , 0 ]tsi z≤n → i₁ ≾ᵢ [ 0 , 0 ]tsi z≤n
≾ᵢ-zero-productˡ {i₁} rel = z≤n , m+n≤o⇒m≤o (max i₁) (proj₂ rel)

≾ᵢ-zero-productʳ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ [ 0 , 0 ]tsi z≤n → i₂ ≾ᵢ [ 0 , 0 ]tsi z≤n
≾ᵢ-zero-productʳ rel = z≤n , m+n≤o⇒n≤o _ (proj₂ rel)


intervals : Grade
intervals = record
             { Carrier = Interval
             ; _·_              = _·ᵢ_
             ; u                = [ 0 , 0 ]tsi z≤n
             ; ·-identityʳ      = ·ᵢ-identityʳ
             ; ·-identityˡ      = ·ᵢ-identityˡ
             ; ·-assoc          = ·ᵢ-assoc
             ; _≾_              = _≾ᵢ_
             ; ·-monoʳ-≾        = λ {i} {i₁} {i₂} rel
                                    → ·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} rel
             ; ·-monoˡ-≾        = λ {i} {i₁} {i₂} rel
                                    → ·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} rel
             ; ≾-refl           = ≤-refl , ≤-refl
             ; ≾-trans          = λ rel₁ rel₂
                                    → ≤-trans (proj₁ rel₂) (proj₁ rel₁) ,
                                      ≤-trans (proj₂ rel₁) (proj₂ rel₂)
             ; _≡?_              = eqᵢ?
             ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ᵢ-zero-productˡ {i₁} {i₂}
             ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ᵢ-zero-productʳ {i₁} {i₂}
             ; of-nat            = λ n → [ n , n ]tsi ≤-refl
             ; of-nat-zero       = eqᵢ refl refl
             ; of-nat-plus       = eqᵢ refl refl
             }
