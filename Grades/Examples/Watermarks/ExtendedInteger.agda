------------------------------------------------------------------------
-- The integers with a greatest element `∞`.                          --
--                                                                    --
-- `ℤ∞` is ordered by `≤` with `∞` greatest, added with `∞`           --
-- absorbing, and joined by the maximum. Addition is monotone and     --
-- distributes over the maximum on both sides; the order is a         --
-- decidable, proof-irrelevant partial order.                         --
------------------------------------------------------------------------

module Grades.Examples.Watermarks.ExtendedInteger where

open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; 0ℤ)
import Data.Integer.Properties as ℤₚ
open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Function.Base using (_∘_)
open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (yes; no; ¬_)

open import Util.Equality

infixl 6 _+∞_ _⊔∞_
infix  4 _≤∞_ _≤∞?_

data ℤ∞ : Set where
  fin : ℤ → ℤ∞
  ∞   : ℤ∞

-- the integer `n`, and its negation

⟨_⟩ : ℕ → ℤ∞
⟨ n ⟩ = fin (+ n)

-⟨_⟩ : ℕ → ℤ∞
-⟨ n ⟩ = fin (ℤ.- (+ n))

0∞ : ℤ∞
0∞ = fin 0ℤ

data _≤∞_ : ℤ∞ → ℤ∞ → Set where
  fin≤fin : ∀ {i j} → i ℤ.≤ j → fin i ≤∞ fin j
  ≤∞-∞    : ∀ {x} → x ≤∞ ∞

_+∞_ : ℤ∞ → ℤ∞ → ℤ∞
fin i +∞ fin j = fin (i ℤ.+ j)
fin _ +∞ ∞     = ∞
∞     +∞ _     = ∞

_⊔∞_ : ℤ∞ → ℤ∞ → ℤ∞
fin i ⊔∞ fin j = fin (i ℤ.⊔ j)
fin _ ⊔∞ ∞     = ∞
∞     ⊔∞ _     = ∞

------------------------------------------------------------------------
-- The order

≤∞-refl : ∀ {x} → x ≤∞ x
≤∞-refl {fin i} = fin≤fin ℤₚ.≤-refl
≤∞-refl {∞}     = ≤∞-∞

≤∞-trans : ∀ {x y z} → x ≤∞ y → y ≤∞ z → x ≤∞ z
≤∞-trans (fin≤fin p) (fin≤fin q) = fin≤fin (ℤₚ.≤-trans p q)
≤∞-trans _           ≤∞-∞        = ≤∞-∞

≤∞-antisym : ∀ {x y} → x ≤∞ y → y ≤∞ x → x ≡ y
≤∞-antisym (fin≤fin p) (fin≤fin q) = cong fin (ℤₚ.≤-antisym p q)
≤∞-antisym ≤∞-∞        ≤∞-∞        = refl

≤∞-irrelevant : ∀ {x y} (p q : x ≤∞ y) → p ≡ q
≤∞-irrelevant (fin≤fin p) (fin≤fin q) = cong fin≤fin (ℤₚ.≤-irrelevant p q)
≤∞-irrelevant ≤∞-∞        ≤∞-∞        = refl

_≤∞?_ : Decidable _≤∞_
fin i ≤∞? fin j with i ℤₚ.≤? j
... | yes p = yes (fin≤fin p)
... | no ¬p = no λ { (fin≤fin p) → ¬p p }
fin _ ≤∞? ∞     = yes ≤∞-∞
∞     ≤∞? fin _ = no λ ()
∞     ≤∞? ∞     = yes ≤∞-∞

≤∞-reflexive : ∀ {x y} → x ≡ y → x ≤∞ y
≤∞-reflexive refl = ≤∞-refl

-- `∞` is the only element above it

∞≤ : ∀ {x} → ∞ ≤∞ x → x ≡ ∞
∞≤ ≤∞-∞ = refl

------------------------------------------------------------------------
-- The maximum is the join

⊔∞-ubˡ : ∀ x y → x ≤∞ x ⊔∞ y
⊔∞-ubˡ (fin i) (fin j) = fin≤fin (ℤₚ.i≤i⊔j i j)
⊔∞-ubˡ (fin _) ∞       = ≤∞-∞
⊔∞-ubˡ ∞       _       = ≤∞-∞

⊔∞-ubʳ : ∀ x y → y ≤∞ x ⊔∞ y
⊔∞-ubʳ (fin i) (fin j) = fin≤fin (ℤₚ.i≤j⊔i i j)
⊔∞-ubʳ (fin _) ∞       = ≤∞-∞
⊔∞-ubʳ ∞       _       = ≤∞-∞

⊔∞-lub : ∀ {x y z} → x ≤∞ z → y ≤∞ z → x ⊔∞ y ≤∞ z
⊔∞-lub (fin≤fin p) (fin≤fin q) = fin≤fin (ℤₚ.⊔-lub p q)
⊔∞-lub _           ≤∞-∞        = ≤∞-∞

⊔∞-mono : ∀ {x x' y y'} → x ≤∞ x' → y ≤∞ y' → x ⊔∞ y ≤∞ x' ⊔∞ y'
⊔∞-mono {x' = x'} {y' = y'} p q =
  ⊔∞-lub (≤∞-trans p (⊔∞-ubˡ x' y')) (≤∞-trans q (⊔∞-ubʳ x' y'))

------------------------------------------------------------------------
-- Addition

+∞-monoˡ : ∀ {x x'} z → x ≤∞ x' → x +∞ z ≤∞ x' +∞ z
+∞-monoˡ (fin k) (fin≤fin p) = fin≤fin (ℤₚ.+-monoˡ-≤ k p)
+∞-monoˡ ∞       (fin≤fin _) = ≤∞-∞
+∞-monoˡ (fin _) ≤∞-∞        = ≤∞-∞
+∞-monoˡ ∞       ≤∞-∞        = ≤∞-∞

+∞-monoʳ : ∀ z {y y'} → y ≤∞ y' → z +∞ y ≤∞ z +∞ y'
+∞-monoʳ (fin k) (fin≤fin p) = fin≤fin (ℤₚ.+-monoʳ-≤ k p)
+∞-monoʳ (fin _) ≤∞-∞        = ≤∞-∞
+∞-monoʳ ∞       _           = ≤∞-∞

+∞-mono : ∀ {x x' y y'} → x ≤∞ x' → y ≤∞ y' → x +∞ y ≤∞ x' +∞ y'
+∞-mono {x' = x'} {y = y} p q = ≤∞-trans (+∞-monoˡ y p) (+∞-monoʳ x' q)

+∞-identityˡ : ∀ x → 0∞ +∞ x ≡ x
+∞-identityˡ (fin i) = cong fin (ℤₚ.+-identityˡ i)
+∞-identityˡ ∞       = refl

+∞-identityʳ : ∀ x → x +∞ 0∞ ≡ x
+∞-identityʳ (fin i) = cong fin (ℤₚ.+-identityʳ i)
+∞-identityʳ ∞       = refl

+∞-assoc : ∀ x y z → (x +∞ y) +∞ z ≡ x +∞ (y +∞ z)
+∞-assoc (fin i) (fin j) (fin k) = cong fin (ℤₚ.+-assoc i j k)
+∞-assoc (fin _) (fin _) ∞       = refl
+∞-assoc (fin _) ∞       _       = refl
+∞-assoc ∞       _       _       = refl

+∞-comm : ∀ x y → x +∞ y ≡ y +∞ x
+∞-comm (fin i) (fin j) = cong fin (ℤₚ.+-comm i j)
+∞-comm (fin _) ∞       = refl
+∞-comm ∞       (fin _) = refl
+∞-comm ∞       ∞       = refl

-- addition distributes over the maximum

+∞-distribˡ-⊔∞ : ∀ x y z → x +∞ (y ⊔∞ z) ≤∞ (x +∞ y) ⊔∞ (x +∞ z)
+∞-distribˡ-⊔∞ (fin i) (fin j) (fin k) =
  fin≤fin (ℤₚ.≤-reflexive (ℤₚ.mono-≤-distrib-⊔ (ℤₚ.+-monoʳ-≤ i) j k))
+∞-distribˡ-⊔∞ (fin _) (fin _) ∞       = ≤∞-∞
+∞-distribˡ-⊔∞ (fin _) ∞       _       = ≤∞-∞
+∞-distribˡ-⊔∞ ∞       _       _       = ≤∞-∞

+∞-distribʳ-⊔∞ : ∀ x y z → (y ⊔∞ z) +∞ x ≤∞ (y +∞ x) ⊔∞ (z +∞ x)
+∞-distribʳ-⊔∞ x y z =
  ≤∞-trans (≤∞-reflexive (+∞-comm (y ⊔∞ z) x))
    (≤∞-trans (+∞-distribˡ-⊔∞ x y z)
      (⊔∞-mono (≤∞-reflexive (+∞-comm x y)) (≤∞-reflexive (+∞-comm x z))))

-- a sum below 0 with a summand at least 0

+∞-≤0ʳ : ∀ {x y} → 0∞ ≤∞ x → x +∞ y ≤∞ 0∞ → y ≤∞ 0∞
+∞-≤0ʳ {x} {y} p q =
  ≤∞-trans (≤∞-reflexive (sym (+∞-identityˡ y))) (≤∞-trans (+∞-monoˡ y p) q)

+∞-≤0ˡ : ∀ {x y} → 0∞ ≤∞ y → x +∞ y ≤∞ 0∞ → x ≤∞ 0∞
+∞-≤0ˡ {x} {y} p q = +∞-≤0ʳ p (≤∞-trans (≤∞-reflexive (+∞-comm y x)) q)
