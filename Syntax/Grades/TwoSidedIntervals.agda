--------------------------------------------
-- Two-sided (closed) intervals as grades --
--------------------------------------------

open import Syntax.Grades

module Syntax.Grades.TwoSidedIntervals (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Algebra.Definitions

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open _≤_

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core

open import Util.Equality

record Interval : Set₀ where
  constructor [_,_]tsi
  field
    min : ℕ
    max : ℕ
    -- min is smaller or equal than max
    fst≤snd : min ≤ max

open Interval public

-- interval addition
_·ᵢ_ : Interval → Interval → Interval
[ min₁ , max₁ ]tsi fst≤snd₁ ·ᵢ [ min₂ , max₂ ]tsi fst≤snd₂ =
  [ min₁ + min₂ , max₁ + max₂ ]tsi
    (+-mono-≤ fst≤snd₁ fst≤snd₂)

infixl 7 _·ᵢ_

-- interval equality
eqᵢ : ∀ {i₁ i₂}
    → min i₁ ≡ min i₂
    → max i₁ ≡ max i₂
    -------------------------
    → i₁ ≡ i₂

eqᵢ {_} {i₂} refl refl = cong (λ x → [ min i₂ , max i₂ ]tsi x) (≤-irrelevant _ _)

i-eq : ∀ {i₁ i₂}
    → i₁ ≡ i₂
    -------------------------
    → (min i₁ ≡ min i₂) × (max i₁ ≡ max i₂)
i-eq refl = refl , refl

-- right and left identity
·ᵢ-identityʳ : (i : Interval) → (i ·ᵢ [ 0 , 0 ]tsi z≤n) ≡ i
·ᵢ-identityʳ i =
  eqᵢ {i ·ᵢ [ 0 , 0 ]tsi z≤n} {i} (+-identityʳ (min i)) ((+-identityʳ (max i)))

·ᵢ-identityˡ : (i : Interval) → ([ 0 , 0 ]tsi z≤n ·ᵢ i) ≡ i
·ᵢ-identityˡ i =
  eqᵢ {[ 0 , 0 ]tsi z≤n ·ᵢ i} {i} (+-identityˡ (min i)) ((+-identityˡ (max i)))

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

-- [ 0 , 0 ]tsi is the minimal element-
[0,0]tsi-minimal : ∀ {i} → i ≾ᵢ [ 0 , 0 ]tsi z≤n → i ≡ [ 0 , 0 ]tsi z≤n
[0,0]tsi-minimal {i} (minrel , maxrel) =
  eqᵢ {i} {[ 0 , 0 ]tsi z≤n} (n≤0⇒n≡0 (≤-trans (fst≤snd i) maxrel)) (n≤0⇒n≡0 maxrel)

-- monotonicity
·ᵢ-monoʳ-≾ᵢ : ∀ {i} → _·ᵢ_ i Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoʳ-≾ᵢ {i} (minrel , maxrel) = +-monoʳ-≤ (min i) minrel , +-monoʳ-≤ (max i) maxrel

·ᵢ-monoˡ-≾ᵢ : ∀ {i} → (_·ᵢ i) Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoˡ-≾ᵢ {i} (minrel , maxrel) = +-monoˡ-≤ (min i) minrel , +-monoˡ-≤ (max i) maxrel

-- irrelevance
≾ᵢ-irrelevant : Irrelevant _≾ᵢ_
≾ᵢ-irrelevant {i₁} {i₂} (relmin , relmax) (predmin , predmax) =
  cong₂ (_,_) (≤-irrelevant relmin predmin) (≤-irrelevant relmax predmax)

-- decidability
_≾ᵢ?_ : Decidable _≾ᵢ_
i₁ ≾ᵢ? i₂ with min i₂ ≤? min i₁ | max i₁ ≤? max i₂
... | yes p | yes q = yes (p , q)
... | yes p | no ¬q = no λ x → ¬q (proj₂ x)
... | no ¬p | _     = no λ x → ¬p (proj₁ x)

eqᵢ? : ∀ {i₁ i₂ : Interval} → Decidable _≡_
eqᵢ? i₁ i₂ with min i₁ ≟ min i₂ | max i₁ ≟ max i₂
... | yes p | yes q = yes (eqᵢ p q)
... | yes p | no ¬q = no λ x → ¬q (proj₂ (i-eq x))
... | no ¬p | _     = no λ x → ¬p (proj₁ (i-eq x))

-- cancellativity
minmax-≡-cancellative : (m₁ m₂ m₃ m₄ m₅ : ℕ)
                      → m₁ + m₃ + m₂ ≡ m₄ + m₃ + m₅
                      → m₁ + m₂ ≡ m₄ + m₅
minmax-≡-cancellative m₁ m₂ m₃ m₄ m₅ eq =
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

·ᵢ-≡-cancellative : ∀ {i₁ i₂ i₃ i₄ i₅} → i₁ ·ᵢ i₃ ·ᵢ i₂ ≡ i₄ ·ᵢ i₃ ·ᵢ i₅ → i₁ ·ᵢ i₂ ≡ i₄ ·ᵢ i₅
·ᵢ-≡-cancellative {i₁} {i₂} {i₃} {i₄} {i₅} eq =
  eqᵢ
    (minmax-≡-cancellative (min i₁) (min i₂) (min i₃) (min i₄) (min i₅) (proj₁ (i-eq eq)))
    (minmax-≡-cancellative (max i₁) (max i₂) (max i₃) (max i₄) (max i₅) (proj₂ (i-eq eq)))

--
·ᵢ-zero-productˡ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ [ 0 , 0 ]tsi z≤n → i₁ ≡ [ 0 , 0 ]tsi z≤n
·ᵢ-zero-productˡ {i₁} {i₂} eq =
  eqᵢ (m+n≡0⇒m≡0 (min i₁) (proj₁ (i-eq eq))) ((m+n≡0⇒m≡0 (max i₁) (proj₂ (i-eq eq))))

·ᵢ-zero-productʳ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ [ 0 , 0 ]tsi z≤n → i₂ ≡ [ 0 , 0 ]tsi z≤n
·ᵢ-zero-productʳ {i₁} {i₂} eq =
  eqᵢ
    (m+n≡0⇒n≡0 (min i₁) {min i₂} (proj₁ (i-eq eq))) ((m+n≡0⇒n≡0 (max i₁) {max i₂} (proj₂ (i-eq eq))))

--equidivisibility
·ᵢ-equidivisible : ∀ {i₁ i₂ i₃ i₄} →
      i₁ ·ᵢ i₂ ≡ i₃ ·ᵢ i₄ →
        Σ[ i ∈ Interval ] (i ≢ [ 0 , 0 ]tsi z≤n × i₁ ·ᵢ i ≡ i₃ × i₂ ≡ i ·ᵢ i₄)
      ⊎ i₁ ≡ i₃ × i₂ ≡ i₄
      ⊎ Σ[ i' ∈ Interval ] (i' ≢ [ 0 , 0 ]tsi z≤n × i₁ ≡ i₃ ·ᵢ i' × i' ·ᵢ i₂ ≡ i₄)

·ᵢ-equidivisible {i₁} {i₂} {i₃} {i₄} eq with min i₁ <? min i₃
·ᵢ-equidivisible {i₁} {i₂} {i₃} {i₄} eq | yes p =
  let i = [ min i₃ ∸ min i₁ , max i₁ ∸ max i₃ ]tsi {!!} in
    inj₁ (
       i
      , {!!}
      , {!!}
      , {!!})
·ᵢ-equidivisible {i₁} {i₂} {i₃} {i₄} eq | no ¬p with min i₁ ≟ min i₃
... | yes q = {!!}
... | no ¬q = {!!}

intervals : Grade
intervals = record
             { Carrier = Interval
             ; _·_ = _·ᵢ_
             ; u = [ 0 , 0 ]tsi z≤n
             ; ·-identityʳ      = ·ᵢ-identityʳ
             ; ·-identityˡ      = ·ᵢ-identityˡ
             ; ·-assoc          = ·ᵢ-assoc
             ; _≾_              = _≾ᵢ_
             ; u-minimal        = [0,0]tsi-minimal
             ; ·-monoʳ-≾        = ·ᵢ-monoʳ-≾ᵢ
             ; ·-monoˡ-≾        = ·ᵢ-monoˡ-≾ᵢ
             ; ≾-refl           = ≤-refl , ≤-refl
             ; ≾-trans          = λ rel₁ rel₂ →
                                    ≤-trans (proj₁ rel₂) (proj₁ rel₁) , ≤-trans (proj₂ rel₁) (proj₂ rel₂)
             ; ≾-irrelevant     = ≾ᵢ-irrelevant
             ; _≾?_             = _≾ᵢ?_
             ; _≡?_             = eqᵢ?
             ; ·-≡-cancellative = ·ᵢ-≡-cancellative
             ; ·-zero-productˡ  = ·ᵢ-zero-productˡ
             ; ·-zero-productʳ  = ·ᵢ-zero-productʳ
             ; ·-equidivisible  = ·ᵢ-equidivisible
             ; embedNat         = λ n → [ n , n ]tsi ≤-refl
             }
