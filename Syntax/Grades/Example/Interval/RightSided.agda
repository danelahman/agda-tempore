------------------------------------------------------------------------
-- (Right) one-sided (closed) intervals as grades.                     --
--                                                                     --
-- A grade `[0, n ]` is an upper bound: "at most `n` time steps".       --
-- Multiplication adds the bounds and the order is `≤` on them, so a    --
-- *larger* bound is the weaker grade -- the mirror image of the        --
-- left-sided intervals.                                               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Interval.RightSided where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Relation.Nullary.Decidable.Core

open import Syntax.Grades

-- type of one-sided intervals

data 𝕀ᵣ : Set where
  [0,_] : ℕ → 𝕀ᵣ

-- equality helpers

eq𝕀ᵣ : ∀ {m n} → m ≡ n → [0, m ] ≡ [0, n ]
eq𝕀ᵣ = cong [0,_]

𝕀ᵣ-inj : ∀ {m n} → [0, m ] ≡ [0, n ] → m ≡ n
𝕀ᵣ-inj refl = refl

-- interval addition

_·ₒ_ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ
[0, m ] ·ₒ [0, n ] = [0, m + n ]

infixl 7 _·ₒ_

-- interval unit

uₒ : 𝕀ᵣ
uₒ = [0, 0 ]

-- interval order

_≾ₒ_ : Rel 𝕀ᵣ lzero
[0, m ] ≾ₒ [0, n ] = m ≤ n

infix 6 _≾ₒ_

-- identity laws

·ₒ-identityʳ : (i : 𝕀ᵣ) → i ·ₒ uₒ ≡ i
·ₒ-identityʳ [0, m ] = eq𝕀ᵣ (+-identityʳ m)

·ₒ-identityˡ : (i : 𝕀ᵣ) → uₒ ·ₒ i ≡ i
·ₒ-identityˡ [0, m ] = eq𝕀ᵣ (+-identityˡ m)

-- associativity

·ₒ-assoc : (i₁ i₂ i₃ : 𝕀ᵣ) → (i₁ ·ₒ i₂) ·ₒ i₃ ≡ i₁ ·ₒ (i₂ ·ₒ i₃)
·ₒ-assoc [0, m ] [0, n ] [0, o ] = eq𝕀ᵣ (+-assoc m n o)

-- monotonicity

·ₒ-monoʳ-≾ₒ : ∀ {i} → (i ·ₒ_) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoʳ-≾ₒ {[0, m ]} {[0, _ ]} {[0, _ ]} = +-monoʳ-≤ m

·ₒ-monoˡ-≾ₒ : ∀ {i} → (_·ₒ i) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoˡ-≾ₒ {[0, m ]} {[0, _ ]} {[0, _ ]} = +-monoˡ-≤ m

-- order properties

≾ₒ-refl : Reflexive _≾ₒ_
≾ₒ-refl {[0, _ ]} = ≤-refl

≾ₒ-trans : Transitive _≾ₒ_
≾ₒ-trans {[0, _ ]} {[0, _ ]} {[0, _ ]} p q = ≤-trans p q

≾ₒ-irrelevant : Irrelevant _≾ₒ_
≾ₒ-irrelevant {[0, _ ]} {[0, _ ]} = ≤-irrelevant

-- decidability

_≡ₒ?_ : Decidable (_≡_ {A = 𝕀ᵣ})
[0, m ] ≡ₒ? [0, n ] with m ≟ n
... | yes p = yes (eq𝕀ᵣ p)
... | no ¬p = no (λ eq → ¬p (𝕀ᵣ-inj eq))

-- cancellativity

·ₒ-≾ₒ-cancellativeˡ : (i₁ i₂ i₃ : 𝕀ᵣ) → (i₁ ·ₒ i₂) ≾ₒ (i₁ ·ₒ i₃) → i₂ ≾ₒ i₃
·ₒ-≾ₒ-cancellativeˡ [0, m₁ ] [0, m₂ ] [0, m₃ ] rel =
  +-cancelˡ-≤ m₁ m₂ m₃ rel

-- zero-product properties

≡ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≡ uₒ → i₁ ≡ uₒ
≡ₒ-zero-productˡ {[0, m ]} {[0, _ ]} eq = eq𝕀ᵣ (m+n≡0⇒m≡0 m (𝕀ᵣ-inj eq))

≡ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≡ uₒ → i₂ ≡ uₒ
≡ₒ-zero-productʳ {[0, m ]} {[0, _ ]} eq = eq𝕀ᵣ (m+n≡0⇒n≡0 m (𝕀ᵣ-inj eq))

≾ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₁ ≾ₒ uₒ
≾ₒ-zero-productˡ {[0, _ ]} {[0, _ ]} rel = m+n≤o⇒m≤o _ rel

≾ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₂ ≾ₒ uₒ
≾ₒ-zero-productʳ {[0, _ ]} {[0, _ ]} rel = m+n≤o⇒n≤o _ rel

-- the grade of (right) one-sided intervals

right-sided-intervals : Grade
right-sided-intervals = record
  { Carrier          = 𝕀ᵣ
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
  ; ≾-irrelevant      = ≾ₒ-irrelevant
  ; of-nat            = [0,_]
  ; of-nat-zero       = refl
  ; of-nat-plus       = refl
  }
