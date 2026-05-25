--------------------------------------------
-- Two-sided (closed) intervals as grades --
--------------------------------------------

open import Syntax.Grades

module Syntax.Grades.TwoSidedInfIntervals (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core

-- type of extended natural numbers

data ℕ∞ : Set where
  `_ : ℕ → ℕ∞
  +∞  : ℕ∞

-- type of intervals

record Interval : Set₀ where
  constructor [_,_]tsi
  field
    min : ℕ
    max : ℕ∞
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

minmax-≤-cancellative : ∀ {m₁ m₂ m₃ m₄ m₅}
                      → m₁ + m₃ + m₂ ≤ m₄ + m₃ + m₅
                      → m₁ + m₂ ≤ m₄ + m₅
minmax-≤-cancellative {m₁} {m₂} {m₃} {m₄} {m₅} rel =
  +-cancelˡ-≤ m₃ (m₁ + m₂) (m₄ + m₅)
    (≤-trans
      (≤-reflexive (trans (sym (+-assoc m₃ m₁ m₂)) (cong (_+ m₂) (+-comm m₃ m₁))))
    (≤-trans
      rel
      (≤-reflexive (trans (cong (_+ m₅) (+-comm m₄ m₃)) (+-assoc m₃ m₄ m₅)))))

minmax-≡-cancellative : ∀ {m₁ m₂ m₃ m₄ m₅}
                      → m₁ + m₃ + m₂ ≡ m₄ + m₃ + m₅
                      → m₁ + m₂ ≡ m₄ + m₅
minmax-≡-cancellative {m₁} {m₂} {m₃} {m₄} {m₅} eq =
  +-cancelˡ-≡ m₃ (m₁ + m₂) (m₄ + m₅)
    (begin
      m₃ + (m₁ + m₂)
    ≡⟨ sym (+-assoc m₃ m₁ m₂) ⟩
      (m₃ + m₁) + m₂
    ≡⟨ cong (_+ m₂) (+-comm m₃ m₁) ⟩
      (m₁ + m₃) + m₂
    ≡⟨ eq ⟩
      (m₄ + m₃) + m₅
    ≡⟨ cong (_+ m₅) (+-comm m₄ m₃) ⟩
      (m₃ + m₄) + m₅
    ≡⟨ (+-assoc m₃ m₄ m₅) ⟩
      m₃ + (m₄ + m₅)
    ∎)

·ᵢ-≡-cancellative : ∀ {i₁ i₂ i₃ i₄ i₅}
                  → i₁ ·ᵢ i₃ ·ᵢ i₂ ≡ i₄ ·ᵢ i₃ ·ᵢ i₅
                  → i₁ ·ᵢ i₂ ≡ i₄ ·ᵢ i₅

·ᵢ-≡-cancellative {i₁} {i₂} {i₃} {i₄} {i₅} eq =
  eqᵢ
    (minmax-≡-cancellative {min i₁} {min i₂} {min i₃} {min i₄} {min i₅} (cong min eq))
    (minmax-≡-cancellative {max i₁} {max i₂} {max i₃} {max i₄} {max i₅} (cong max eq))

·ᵢ-≾ᵢ-cancellative : ∀ {i₁ i₂ i₃ i₄ i₅}
                  → (i₁ ·ᵢ i₃ ·ᵢ i₂) ≾ᵢ (i₄ ·ᵢ i₃ ·ᵢ i₅)
                  → (i₁ ·ᵢ i₂) ≾ᵢ (i₄ ·ᵢ i₅)

·ᵢ-≾ᵢ-cancellative {i₁} {i₂} {i₃} {i₄} {i₅} rel =
  minmax-≤-cancellative {min i₄} {min i₅} {min i₃} {min i₁} {min i₂} (proj₁ rel) ,
  minmax-≤-cancellative {max i₁} {max i₂} {max i₃} {max i₄} {max i₅} (proj₂ rel)

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
             ; _·_ = _·ᵢ_
             ; u = [ 0 , 0 ]tsi z≤n
             ; ·-identityʳ = ·ᵢ-identityʳ
             ; ·-identityˡ = ·ᵢ-identityˡ
             ; ·-assoc = ·ᵢ-assoc
             ; _≾_ = _≾ᵢ_
             ; ·-monoʳ-≾ = λ {i} {i₁} {i₂} rel
                             → ·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} rel
             ; ·-monoˡ-≾ = λ {i} {i₁} {i₂} rel
                             → ·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} rel
             ; ≾-refl = ≤-refl , ≤-refl
             ; ≾-trans = λ rel₁ rel₂
                           → ≤-trans (proj₁ rel₂) (proj₁ rel₁) , ≤-trans (proj₂ rel₁) (proj₂ rel₂)
             ; ≾-irrelevant = λ {i₁} {i₂} rel₁ rel₂
                                → ≾ᵢ-irrelevant {i₁} {i₂} rel₁ rel₂
             ; _≡?_ = eqᵢ?
             ; ·-≡-cancellative = λ {i₁} {i₂} {i₃} {i₄} {i₅} eq
                                    → ·ᵢ-≡-cancellative {i₁} {i₂} {i₃} {i₄} {i₅} eq
             ; ·-≾-cancellative = λ {i₁} {i₂} {i₃} {i₄} {i₅} rel
                                    → ·ᵢ-≾ᵢ-cancellative {i₁} {i₂} {i₃} {i₄} {i₅} rel
             ; ≡-zero-productˡ = ≡ᵢ-zero-productˡ
             ; ≡-zero-productʳ = λ {i₁} {i₂} → ≡ᵢ-zero-productʳ {i₁} {i₂}
             ; ≾-zero-productˡ = λ {i₁} {i₂} → ≾ᵢ-zero-productˡ {i₁} {i₂}
             ; ≾-zero-productʳ = λ {i₁} {i₂} → ≾ᵢ-zero-productʳ {i₁} {i₂}
             ; of-nat = λ n → [ n , n ]tsi ≤-refl
             ; of-nat-zero = eqᵢ refl refl
             ; of-nat-plus = λ {m} {n} → eqᵢ refl refl
             }
