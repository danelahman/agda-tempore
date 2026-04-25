--------------------------------------------
-- One-sided (closed) intervals as grades --
--------------------------------------------

open import Syntax.Grades

module Syntax.Grades.OneSidedIntervals (Grades : GradeSystem) where

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

-- type of one-sided intervals

data 𝕀 : Set where
  [_,+∞⟩ : ℕ → 𝕀

-- equality helpers

eq𝕀 : ∀ {m n} → m ≡ n → [ m ,+∞⟩ ≡ [ n ,+∞⟩
eq𝕀 = cong [_,+∞⟩

𝕀-inj : ∀ {m n} → [ m ,+∞⟩ ≡ [ n ,+∞⟩ → m ≡ n
𝕀-inj refl = refl

-- interval addition

_·ₒ_ : 𝕀 → 𝕀 → 𝕀
[ m ,+∞⟩ ·ₒ [ n ,+∞⟩ = [ m + n ,+∞⟩

infixl 7 _·ₒ_

-- interval unit

uₒ : 𝕀
uₒ = [ 0 ,+∞⟩

-- interval order

_≾ₒ_ : Rel 𝕀 lzero
[ m ,+∞⟩ ≾ₒ [ n ,+∞⟩ = n ≤ m

infix 6 _≾ₒ_

-- identity laws

·ₒ-identityʳ : (i : 𝕀) → i ·ₒ uₒ ≡ i
·ₒ-identityʳ [ m ,+∞⟩ = eq𝕀 (+-identityʳ m)

·ₒ-identityˡ : (i : 𝕀) → uₒ ·ₒ i ≡ i
·ₒ-identityˡ [ m ,+∞⟩ = eq𝕀 (+-identityˡ m)

-- associativity

·ₒ-assoc : (i₁ i₂ i₃ : 𝕀) → (i₁ ·ₒ i₂) ·ₒ i₃ ≡ i₁ ·ₒ (i₂ ·ₒ i₃)
·ₒ-assoc [ m ,+∞⟩ [ n ,+∞⟩ [ o ,+∞⟩ = eq𝕀 (+-assoc m n o)

-- monotonicity

·ₒ-monoʳ-≾ₒ : ∀ {i} → (i ·ₒ_) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoʳ-≾ₒ {[ m ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} = +-monoʳ-≤ m

·ₒ-monoˡ-≾ₒ : ∀ {i} → (_·ₒ i) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoˡ-≾ₒ {[ m ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} = +-monoˡ-≤ m

-- order properties

≾ₒ-refl : Reflexive _≾ₒ_
≾ₒ-refl {[ _ ,+∞⟩} = ≤-refl

≾ₒ-trans : Transitive _≾ₒ_
≾ₒ-trans {[ _ ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} p q = ≤-trans q p

≾ₒ-irrelevant : Irrelevant _≾ₒ_
≾ₒ-irrelevant {[ _ ,+∞⟩} {[ _ ,+∞⟩} = ≤-irrelevant

-- decidability

_≡ₒ?_ : Decidable (_≡_ {A = 𝕀})
[ m ,+∞⟩ ≡ₒ? [ n ,+∞⟩ with m ≟ n
... | yes p = yes (eq𝕀 p)
... | no ¬p = no (λ eq → ¬p (𝕀-inj eq))

-- cancellativity (ℕ-level auxiliaries)

·ₒ-≡-cancellative-aux : ∀ {m₁ m₂ m₃ m₄ m₅}
                       → m₁ + m₃ + m₂ ≡ m₄ + m₃ + m₅
                       → m₁ + m₂ ≡ m₄ + m₅
·ₒ-≡-cancellative-aux {m₁} {m₂} {m₃} {m₄} {m₅} eq =
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
    ≡⟨ +-assoc m₃ m₄ m₅ ⟩
      m₃ + (m₄ + m₅)
    ∎)

·ₒ-≾ₒ-cancellative-aux : ∀ {m₁ m₂ m₃ m₄ m₅}
                        → m₁ + m₃ + m₂ ≤ m₄ + m₃ + m₅
                        → m₁ + m₂ ≤ m₄ + m₅
·ₒ-≾ₒ-cancellative-aux {m₁} {m₂} {m₃} {m₄} {m₅} rel =
  +-cancelˡ-≤ m₃ (m₁ + m₂) (m₄ + m₅)
    (≤-trans
      (≤-reflexive (trans (sym (+-assoc m₃ m₁ m₂)) (cong (_+ m₂) (+-comm m₃ m₁))))
    (≤-trans
      rel
      (≤-reflexive (trans (cong (_+ m₅) (+-comm m₄ m₃)) (+-assoc m₃ m₄ m₅)))))

·ₒ-≡-cancellative : ∀ {i₁ i₂ i₃ i₄ i₅ : 𝕀}
                   → i₁ ·ₒ i₃ ·ₒ i₂ ≡ i₄ ·ₒ i₃ ·ₒ i₅
                   → i₁ ·ₒ i₂ ≡ i₄ ·ₒ i₅
·ₒ-≡-cancellative {[ m₁ ,+∞⟩} {[ m₂ ,+∞⟩} {[ m₃ ,+∞⟩} {[ m₄ ,+∞⟩} {[ m₅ ,+∞⟩} eq =
  eq𝕀 (·ₒ-≡-cancellative-aux {m₁} {m₂} {m₃} {m₄} {m₅} (𝕀-inj eq))

·ₒ-≾ₒ-cancellative : ∀ {i₁ i₂ i₃ i₄ i₅ : 𝕀}
                    → i₁ ·ₒ i₃ ·ₒ i₂ ≾ₒ i₄ ·ₒ i₃ ·ₒ i₅
                    → i₁ ·ₒ i₂ ≾ₒ i₄ ·ₒ i₅
·ₒ-≾ₒ-cancellative {[ m₁ ,+∞⟩} {[ m₂ ,+∞⟩} {[ m₃ ,+∞⟩} {[ m₄ ,+∞⟩} {[ m₅ ,+∞⟩} =
  ·ₒ-≾ₒ-cancellative-aux {m₄} {m₅} {m₃} {m₁} {m₂}

-- zero-product properties

≡ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≡ uₒ → i₁ ≡ uₒ
≡ₒ-zero-productˡ {[ m ,+∞⟩} {[ _ ,+∞⟩} eq = eq𝕀 (m+n≡0⇒m≡0 m (𝕀-inj eq))

≡ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≡ uₒ → i₂ ≡ uₒ
≡ₒ-zero-productʳ {[ m ,+∞⟩} {[ _ ,+∞⟩} eq = eq𝕀 (m+n≡0⇒n≡0 m (𝕀-inj eq))

≾ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₁ ≾ₒ uₒ
≾ₒ-zero-productˡ {[ _ ,+∞⟩} {[ _ ,+∞⟩} _ = z≤n

≾ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₂ ≾ₒ uₒ
≾ₒ-zero-productʳ {[ _ ,+∞⟩} {[ _ ,+∞⟩} _ = z≤n

-- the grade of one-sided intervals

one-sided-intervals : Grade
one-sided-intervals = record
  { Carrier          = 𝕀
  ; _·_              = _·ₒ_
  ; u                = uₒ
  ; ·-identityʳ      = ·ₒ-identityʳ
  ; ·-identityˡ      = ·ₒ-identityˡ
  ; ·-assoc          = ·ₒ-assoc
  ; _≾_              = _≾ₒ_
  ; ·-monoʳ-≾        = ·ₒ-monoʳ-≾ₒ
  ; ·-monoˡ-≾        = ·ₒ-monoˡ-≾ₒ
  ; ≾-refl           = ≾ₒ-refl
  ; ≾-trans          = ≾ₒ-trans
  ; ≾-irrelevant     = ≾ₒ-irrelevant
  ; _≡?_             = _≡ₒ?_
  ; ·-≡-cancellative = ·ₒ-≡-cancellative
  ; ·-≾-cancellative = ·ₒ-≾ₒ-cancellative
  ; ≡-zero-productˡ  = ≡ₒ-zero-productˡ
  ; ≡-zero-productʳ  = ≡ₒ-zero-productʳ
  ; ≾-zero-productˡ  = ≾ₒ-zero-productˡ
  ; ≾-zero-productʳ  = ≾ₒ-zero-productʳ
  ; of-nat           = [_,+∞⟩
  ; of-nat-zero      = refl
  ; of-nat-plus      = refl
  }
