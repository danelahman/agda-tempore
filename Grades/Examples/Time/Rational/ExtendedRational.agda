------------------------------------------------------------------------
-- The extended non-negative rationals ℚ∞.                            --
--                                                                    --
-- The dense counterpart of `Time.ExtendedNat`: `↑ q` is the finite   --
-- value `q : ℚ≥0` and `∞` the point at infinity, absorbing for       --
-- addition and greatest in the order. The lemmas are named after     --
-- their `ExtendedNat` counterparts.                                  --
--                                                                    --
-- `ℕ∞→ℚ∞` embeds the extended naturals, preserving addition, the     --
-- order and the maximum.                                             --
------------------------------------------------------------------------

module Grades.Examples.Time.Rational.ExtendedRational where

open import Data.Empty
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Util.Equality

open import Util.NonNegativeRational public

import Grades.Examples.Time.ExtendedNat as ℕ∞

------------------------------------------------------------------------
-- The carrier

data ℚ∞ : Set₀ where
  ↑_ : ℚ≥0 → ℚ∞
  ∞  : ℚ∞

infix 8 ↑_

↑-inj : ∀ {p q} → ↑ p ≡ ↑ q → p ≡ q
↑-inj refl = refl

------------------------------------------------------------------------
-- Addition (∞ is absorbing)

_+∞_ : ℚ∞ → ℚ∞ → ℚ∞
↑ p +∞ ↑ q = ↑ (p + q)
↑ p +∞ ∞   = ∞
∞   +∞ _   = ∞

infixl 7 _+∞_

+∞-identityʳ : ∀ a → a +∞ ↑ 0ᵈ ≡ a
+∞-identityʳ (↑ p) = cong ↑_ (+-identityʳ p)
+∞-identityʳ ∞     = refl

+∞-identityˡ : ∀ a → ↑ 0ᵈ +∞ a ≡ a
+∞-identityˡ (↑ p) = cong ↑_ (+-identityˡ p)
+∞-identityˡ ∞     = refl

+∞-assoc : ∀ a b c → (a +∞ b) +∞ c ≡ a +∞ (b +∞ c)
+∞-assoc (↑ x) (↑ y) (↑ z) = cong ↑_ (+-assoc x y z)
+∞-assoc (↑ _) (↑ _) ∞     = refl
+∞-assoc (↑ _) ∞     _     = refl
+∞-assoc ∞     _     _     = refl

+∞-comm : ∀ a b → a +∞ b ≡ b +∞ a
+∞-comm (↑ x) (↑ y) = cong ↑_ (+-comm x y)
+∞-comm (↑ _) ∞     = refl
+∞-comm ∞     (↑ _) = refl
+∞-comm ∞     ∞     = refl

------------------------------------------------------------------------
-- The order (everything is below ∞)

_≤∞_ : ℚ∞ → ℚ∞ → Set₀
↑ p ≤∞ ↑ q = p ≤ q
↑ _ ≤∞ ∞   = ⊤
∞   ≤∞ ↑ _ = ⊥
∞   ≤∞ ∞   = ⊤

infix 6 _≤∞_

≤∞-∞ : ∀ a → a ≤∞ ∞
≤∞-∞ (↑ _) = tt
≤∞-∞ ∞     = tt

≤∞-refl : ∀ {a} → a ≤∞ a
≤∞-refl {↑ _} = ≤-refl
≤∞-refl {∞}   = tt

≤∞-trans : ∀ {a b c} → a ≤∞ b → b ≤∞ c → a ≤∞ c
≤∞-trans {↑ _} {↑ _} {↑ _} p q = ≤-trans p q
≤∞-trans {↑ _} {↑ _} {∞}   p q = tt
≤∞-trans {↑ _} {∞}   {↑ _} p ()
≤∞-trans {↑ _} {∞}   {∞}   p q = tt
≤∞-trans {∞}   {↑ _} {_}   () q
≤∞-trans {∞}   {∞}   {↑ _} p ()
≤∞-trans {∞}   {∞}   {∞}   p q = tt

≤∞-antisym : {a b : ℚ∞} → a ≤∞ b → b ≤∞ a → a ≡ b
≤∞-antisym {↑ _} {↑ _} p q = cong ↑_ (≤-antisym p q)
≤∞-antisym {↑ _} {∞}   p ()
≤∞-antisym {∞}   {↑ _} () q
≤∞-antisym {∞}   {∞}   p q = refl

≤∞-reflexive : {a b : ℚ∞} → a ≡ b → a ≤∞ b
≤∞-reflexive {a} refl = ≤∞-refl {a}

infix 4 _≤∞?_

_≤∞?_ : (a b : ℚ∞) → Dec (a ≤∞ b)
(↑ p) ≤∞? (↑ q) = p ≤? q
(↑ _) ≤∞? ∞     = yes tt
∞     ≤∞? (↑ _) = no λ ()
∞     ≤∞? ∞     = yes tt

≤∞-irrelevant : {a b : ℚ∞} → (p q : a ≤∞ b) → p ≡ q
≤∞-irrelevant {↑ _} {↑ _} p q = ≤-irrelevant p q
≤∞-irrelevant {↑ _} {∞}   p q = refl
≤∞-irrelevant {∞}   {↑ _} () q
≤∞-irrelevant {∞}   {∞}   p q = refl

+∞-mono-≤∞ : {a b c d : ℚ∞} → a ≤∞ c → b ≤∞ d → (a +∞ b) ≤∞ (c +∞ d)
+∞-mono-≤∞ {↑ _} {↑ _} {↑ _} {↑ _} p q = +-mono-≤ p q
+∞-mono-≤∞ {↑ _} {↑ _} {↑ _} {∞}   p q = tt
+∞-mono-≤∞ {↑ _} {∞}   {↑ _} {↑ _} p ()
+∞-mono-≤∞ {↑ _} {∞}   {↑ _} {∞}   p q = tt
+∞-mono-≤∞ {↑ x} {b}   {∞}   {d}   p q = ≤∞-∞ (↑ x +∞ b)
+∞-mono-≤∞ {∞}   {b}   {↑ _} {d}   () q
+∞-mono-≤∞ {∞}   {b}   {∞}   {d}   p q = tt

------------------------------------------------------------------------
-- Maximum (∞ is greatest)

_⊔∞_ : ℚ∞ → ℚ∞ → ℚ∞
↑ p ⊔∞ ↑ q = ↑ (p ⊔ q)
↑ _ ⊔∞ ∞   = ∞
∞   ⊔∞ _   = ∞

infixl 7 _⊔∞_

⊔∞-ubˡ : (a b : ℚ∞) → a ≤∞ a ⊔∞ b
⊔∞-ubˡ (↑ p) (↑ q) = ⊔-ubˡ p q
⊔∞-ubˡ (↑ _) ∞     = tt
⊔∞-ubˡ ∞     _     = tt

⊔∞-ubʳ : (a b : ℚ∞) → b ≤∞ a ⊔∞ b
⊔∞-ubʳ (↑ p) (↑ q) = ⊔-ubʳ p q
⊔∞-ubʳ (↑ _) ∞     = tt
⊔∞-ubʳ ∞     (↑ _) = tt
⊔∞-ubʳ ∞     ∞     = tt

⊔∞-lub : {a b c : ℚ∞} → a ≤∞ c → b ≤∞ c → a ⊔∞ b ≤∞ c
⊔∞-lub {↑ _} {↑ _} {↑ _} p q = ⊔-lub p q
⊔∞-lub {↑ _} {↑ _} {∞}   p q = tt
⊔∞-lub {↑ _} {∞}   {∞}   p q = tt
⊔∞-lub {∞}   {_}   {∞}   p q = tt

+∞-distribˡ-⊔∞ : (a b c : ℚ∞) → a +∞ (b ⊔∞ c) ≡ (a +∞ b) ⊔∞ (a +∞ c)
+∞-distribˡ-⊔∞ (↑ x) (↑ y) (↑ z) = cong ↑_ (+-distribˡ-⊔ x y z)
+∞-distribˡ-⊔∞ (↑ _) (↑ _) ∞     = refl
+∞-distribˡ-⊔∞ (↑ _) ∞     _     = refl
+∞-distribˡ-⊔∞ ∞     _     _     = refl

+∞-distribʳ-⊔∞ : (a b c : ℚ∞) → (b ⊔∞ c) +∞ a ≡ (b +∞ a) ⊔∞ (c +∞ a)
+∞-distribʳ-⊔∞ (↑ x) (↑ y) (↑ z) = cong ↑_ (+-distribʳ-⊔ x y z)
+∞-distribʳ-⊔∞ ∞     (↑ _) (↑ _) = refl
+∞-distribʳ-⊔∞ (↑ _) (↑ _) ∞     = refl
+∞-distribʳ-⊔∞ ∞     (↑ _) ∞     = refl
+∞-distribʳ-⊔∞ _     ∞     _     = refl

------------------------------------------------------------------------
-- ↑ 0ᵈ is the least element
--
-- A sum within `↑ 0ᵈ` has both summands within it, the summands being
-- non-negative and neither being ∞.

+∞-≤∞-0ˡ : ∀ {a b} → (a +∞ b) ≤∞ ↑ 0ᵈ → a ≤∞ ↑ 0ᵈ
+∞-≤∞-0ˡ {↑ x} {↑ y} p = +-≤0ˡ {x} {y} p
+∞-≤∞-0ˡ {↑ _} {∞}   ()
+∞-≤∞-0ˡ {∞}   {_}   ()

+∞-≤∞-0ʳ : ∀ {a b} → (a +∞ b) ≤∞ ↑ 0ᵈ → b ≤∞ ↑ 0ᵈ
+∞-≤∞-0ʳ {↑ x} {↑ y} p = +-≤0ʳ {x} {y} p
+∞-≤∞-0ʳ {↑ _} {∞}   ()
+∞-≤∞-0ʳ {∞}   {_}   ()

≤∞-↑0 : ∀ {a} → a ≤∞ ↑ 0ᵈ → a ≡ ↑ 0ᵈ
≤∞-↑0 {↑ _} p = cong ↑_ (≤0⇒≡0 p)
≤∞-↑0 {∞}   ()

------------------------------------------------------------------------
-- The closure under addition: `0` absorbs its own iteration, and of the
-- other values only `∞` does

closure : (p : ℚ≥0) → Dec (p ≤ 0ᵈ) → ℚ∞
closure p (yes _) = ↑ p
closure p (no _)  = ∞

plus∞ : ℚ∞ → ℚ∞
plus∞ (↑ p) = closure p (p ≤? 0ᵈ)
plus∞ ∞     = ∞

≤∞-plus∞ : ∀ a → a ≤∞ plus∞ a
≤∞-plus∞ (↑ p) with p ≤? 0ᵈ
... | yes _ = ≤-refl
... | no _  = tt
≤∞-plus∞ ∞ = tt

plus∞-iter : ∀ a → (plus∞ a +∞ plus∞ a) ≤∞ plus∞ a
plus∞-iter (↑ p) with p ≤? 0ᵈ
... | yes r = ≤-trans (+-mono-≤ r r) (≤-trans (≤-reflexive (+-identityʳ 0ᵈ)) (0≤ p))
... | no _  = tt
plus∞-iter ∞ = tt

plus∞-least : ∀ {a v} → a ≤∞ v → (v +∞ v) ≤∞ v → plus∞ a ≤∞ v
plus∞-least {↑ p} {v} q₁ q₂ with p ≤? 0ᵈ
plus∞-least {↑ p} {v}   q₁ q₂ | yes _ = q₁
plus∞-least {↑ p} {↑ m} q₁ q₂ | no ¬r = ⊥-elim (¬r (≤-trans q₁ (+-self q₂)))
plus∞-least {↑ p} {∞}   q₁ q₂ | no _  = tt
plus∞-least {∞}   {∞}   q₁ q₂ = tt

-- a value that a summand does not move, the summand's closure does not
-- move either

plus∞-indˡ : ∀ {a b} → (a +∞ b) ≤∞ b → (plus∞ a +∞ b) ≤∞ b
plus∞-indˡ {↑ p} {b} q with p ≤? 0ᵈ
plus∞-indˡ {↑ p} {b}   q | yes _ = q
plus∞-indˡ {↑ p} {↑ m} q | no ¬r = ⊥-elim (¬r (+-absorbˡ q))
plus∞-indˡ {↑ p} {∞}   q | no _  = tt
plus∞-indˡ {∞}   {↑ _} ()
plus∞-indˡ {∞}   {∞}   q = tt

plus∞-indʳ : ∀ {a b} → (b +∞ a) ≤∞ b → (b +∞ plus∞ a) ≤∞ b
plus∞-indʳ {a} {b} q =
  subst (_≤∞ b) (+∞-comm (plus∞ a) b) (plus∞-indˡ (subst (_≤∞ b) (+∞-comm b a) q))

------------------------------------------------------------------------
-- The embedding of the extended naturals

ℕ∞→ℚ∞ : ℕ∞.ℕ∞ → ℚ∞
ℕ∞→ℚ∞ (ℕ∞.↑ n) = ↑ (# n)
ℕ∞→ℚ∞ ℕ∞.∞     = ∞

ℕ∞→ℚ∞-+ : ∀ a b → ℕ∞→ℚ∞ (a ℕ∞.+∞ b) ≡ ℕ∞→ℚ∞ a +∞ ℕ∞→ℚ∞ b
ℕ∞→ℚ∞-+ (ℕ∞.↑ m) (ℕ∞.↑ n) = cong ↑_ (#-+ m n)
ℕ∞→ℚ∞-+ (ℕ∞.↑ _) ℕ∞.∞     = refl
ℕ∞→ℚ∞-+ ℕ∞.∞     _        = refl

ℕ∞→ℚ∞-mono : ∀ {a b} → a ℕ∞.≤∞ b → ℕ∞→ℚ∞ a ≤∞ ℕ∞→ℚ∞ b
ℕ∞→ℚ∞-mono {ℕ∞.↑ _} {ℕ∞.↑ _} p = #-mono-≤ p
ℕ∞→ℚ∞-mono {ℕ∞.↑ _} {ℕ∞.∞}   p = tt
ℕ∞→ℚ∞-mono {ℕ∞.∞}   {ℕ∞.↑ _} ()
ℕ∞→ℚ∞-mono {ℕ∞.∞}   {ℕ∞.∞}   p = tt

ℕ∞→ℚ∞-⊔ : ∀ a b → ℕ∞→ℚ∞ (a ℕ∞.⊔∞ b) ≡ ℕ∞→ℚ∞ a ⊔∞ ℕ∞→ℚ∞ b
ℕ∞→ℚ∞-⊔ (ℕ∞.↑ m) (ℕ∞.↑ n) = cong ↑_ (#-⊔ m n)
ℕ∞→ℚ∞-⊔ (ℕ∞.↑ _) ℕ∞.∞     = refl
ℕ∞→ℚ∞-⊔ ℕ∞.∞     _        = refl
