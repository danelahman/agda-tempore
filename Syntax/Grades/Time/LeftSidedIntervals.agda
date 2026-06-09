---------------------------------------------------
-- (Left) One-sided (closed) intervals as grades --
---------------------------------------------------

module Syntax.Grades.Time.LeftSidedIntervals where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Syntax.Grades

open import Util.Equality

-- type of (left) one-sided intervals

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

-- cancellativity

·ₒ-≾ₒ-cancellativeˡ : (i₁ i₂ i₃ : 𝕀) → (i₁ ·ₒ i₂) ≾ₒ (i₁ ·ₒ i₃) → i₂ ≾ₒ i₃
·ₒ-≾ₒ-cancellativeˡ [ m₁ ,+∞⟩ [ m₂ ,+∞⟩ [ m₃ ,+∞⟩ rel =
  +-cancelˡ-≤ m₁ m₃ m₂ rel


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
  ; _·_               = _·ₒ_
  ; u                 = uₒ
  ; ·-identityʳ       = ·ₒ-identityʳ
  ; ·-identityˡ       = ·ₒ-identityˡ
  ; ·-assoc           = ·ₒ-assoc
  ; _≾_               = _≾ₒ_
  ; ·-monoʳ-≾         = ·ₒ-monoʳ-≾ₒ
  ; ·-monoˡ-≾         = ·ₒ-monoˡ-≾ₒ
  ; ≾-refl            = ≾ₒ-refl
  ; ≾-trans           = ≾ₒ-trans
  ; _≡?_              = _≡ₒ?_
  ; ≾-zero-productˡ   = ≾ₒ-zero-productˡ
  ; ≾-zero-productʳ   = ≾ₒ-zero-productʳ
  ; of-nat            = [_,+∞⟩
  ; of-nat-zero       = refl
  ; of-nat-plus       = refl
  }
