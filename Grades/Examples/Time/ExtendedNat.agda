------------------------------------------------------------------------
-- The extended natural numbers ℕ∞.                                   --
--                                                                    --
-- `↑ n` is the finite value `n` and `∞` the point at infinity,       --
-- absorbing for addition and greatest in the order. ℕ∞ is an ordered --
-- monoid in its own right; it provides the endpoints of the          --
-- upper bounds and the upper endpoints of `Interval∞`.               --
------------------------------------------------------------------------

module Grades.Examples.Time.ExtendedNat where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Unit using (⊤; tt)

open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Util.Equality

------------------------------------------------------------------------
-- The carrier

-- `↑ n` is the finite value `n`, while `∞` is the point at infinity.

data ℕ∞ : Set₀ where
  ↑_ : ℕ → ℕ∞
  ∞  : ℕ∞

infix 8 ↑_

↑-inj : ∀ {m n} → ↑ m ≡ ↑ n → m ≡ n
↑-inj refl = refl

------------------------------------------------------------------------
-- Addition (∞ is absorbing)

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
↑ m +∞ ↑ n = ↑ (m + n)
↑ m +∞ ∞   = ∞
∞   +∞ _   = ∞

infixl 7 _+∞_

-- addition identities and associativity

+∞-identityʳ : ∀ a → a +∞ ↑ 0 ≡ a
+∞-identityʳ (↑ m) = cong ↑_ (+-identityʳ m)
+∞-identityʳ ∞     = refl

+∞-identityˡ : ∀ a → ↑ 0 +∞ a ≡ a
+∞-identityˡ (↑ _) = refl
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

_≤∞_ : ℕ∞ → ℕ∞ → Set₀
↑ m ≤∞ ↑ n = m ≤ n
↑ m ≤∞ ∞   = ⊤
∞   ≤∞ ↑ n = ⊥
∞   ≤∞ ∞   = ⊤

infix 6 _≤∞_

-- everything is ≤∞ ∞

≤∞-∞ : ∀ a → a ≤∞ ∞
≤∞-∞ (↑ _) = tt
≤∞-∞ ∞     = tt

-- order is a partial order

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

-- ∞ is comparable only with itself, so mutual bounds force equality

≤∞-antisym : {a b : ℕ∞} → a ≤∞ b → b ≤∞ a → a ≡ b
≤∞-antisym {↑ _} {↑ _} p q = cong ↑_ (≤-antisym p q)
≤∞-antisym {↑ _} {∞}   p ()
≤∞-antisym {∞}   {↑ _} () q
≤∞-antisym {∞}   {∞}   p q = refl

-- equal endpoints are related

≤∞-reflexive : {a b : ℕ∞} → a ≡ b → a ≤∞ b
≤∞-reflexive {a} refl = ≤∞-refl {a}

-- order is decidable

infix 4 _≤∞?_

_≤∞?_ : (a b : ℕ∞) → Dec (a ≤∞ b)
(↑ m) ≤∞? (↑ n) = m ≤? n
(↑ _) ≤∞? ∞     = yes tt
∞     ≤∞? (↑ _) = no λ ()
∞     ≤∞? ∞     = yes tt

-- order is irrelevant

≤∞-irrelevant : {a b : ℕ∞} → (p q : a ≤∞ b) → p ≡ q
≤∞-irrelevant {↑ _} {↑ _} p q = ≤-irrelevant p q
≤∞-irrelevant {↑ _} {∞}   p q = refl
≤∞-irrelevant {∞}   {↑ _} () q
≤∞-irrelevant {∞}   {∞}   p q = refl

-- addition is monotone

+∞-mono-≤∞ : {a b c d : ℕ∞} → a ≤∞ c → b ≤∞ d → (a +∞ b) ≤∞ (c +∞ d)
+∞-mono-≤∞ {↑ _} {↑ _} {↑ _} {↑ _} p q = +-mono-≤ p q
+∞-mono-≤∞ {↑ _} {↑ _} {↑ _} {∞}   p q = tt
+∞-mono-≤∞ {↑ _} {∞}   {↑ _} {↑ _} p ()
+∞-mono-≤∞ {↑ _} {∞}   {↑ _} {∞}   p q = tt
+∞-mono-≤∞ {↑ x} {b}   {∞}   {d}   p q = ≤∞-∞ (↑ x +∞ b)
+∞-mono-≤∞ {∞}   {b}   {↑ _} {d}   () q
+∞-mono-≤∞ {∞}   {b}   {∞}   {d}   p q = tt

------------------------------------------------------------------------
-- Maximum (∞ is greatest)

_⊔∞_ : ℕ∞ → ℕ∞ → ℕ∞
↑ m ⊔∞ ↑ n = ↑ (m ⊔ n)
↑ _ ⊔∞ ∞   = ∞
∞   ⊔∞ _   = ∞

infixl 7 _⊔∞_

-- the maximum is the least upper bound

⊔∞-ubˡ : (a b : ℕ∞) → a ≤∞ a ⊔∞ b
⊔∞-ubˡ (↑ m) (↑ n) = m≤m⊔n m n
⊔∞-ubˡ (↑ _) ∞     = tt
⊔∞-ubˡ ∞     _     = tt

⊔∞-ubʳ : (a b : ℕ∞) → b ≤∞ a ⊔∞ b
⊔∞-ubʳ (↑ m) (↑ n) = m≤n⊔m m n
⊔∞-ubʳ (↑ _) ∞     = tt
⊔∞-ubʳ ∞     (↑ _) = tt
⊔∞-ubʳ ∞     ∞     = tt

⊔∞-lub : {a b c : ℕ∞} → a ≤∞ c → b ≤∞ c → a ⊔∞ b ≤∞ c
⊔∞-lub {↑ _} {↑ _} {↑ _} p q = ⊔-lub p q
⊔∞-lub {↑ _} {↑ _} {∞}   p q = tt
⊔∞-lub {↑ _} {∞}   {∞}   p q = tt
⊔∞-lub {∞}   {_}   {∞}   p q = tt

-- addition distributes over the maximum

+∞-distribˡ-⊔∞ : (a b c : ℕ∞) → a +∞ (b ⊔∞ c) ≡ (a +∞ b) ⊔∞ (a +∞ c)
+∞-distribˡ-⊔∞ (↑ x) (↑ y) (↑ z) = cong ↑_ (+-distribˡ-⊔ x y z)
+∞-distribˡ-⊔∞ (↑ _) (↑ _) ∞     = refl
+∞-distribˡ-⊔∞ (↑ _) ∞     _     = refl
+∞-distribˡ-⊔∞ ∞     _     _     = refl

+∞-distribʳ-⊔∞ : (a b c : ℕ∞) → (b ⊔∞ c) +∞ a ≡ (b +∞ a) ⊔∞ (c +∞ a)
+∞-distribʳ-⊔∞ (↑ x) (↑ y) (↑ z) = cong ↑_ (+-distribʳ-⊔ x y z)
+∞-distribʳ-⊔∞ ∞     (↑ _) (↑ _) = refl
+∞-distribʳ-⊔∞ (↑ _) (↑ _) ∞     = refl
+∞-distribʳ-⊔∞ ∞     (↑ _) ∞     = refl
+∞-distribʳ-⊔∞ _     ∞     _     = refl

------------------------------------------------------------------------
-- ↑ 0 is the least element
--
-- The zero-product properties of the grades are built from these: a
-- sum within `↑ 0` has no summand ∞.

-- a finite sum that is ↑ 0 forces both summands below ↑ 0

+∞-≤∞-0ˡ : ∀ {a b} → (a +∞ b) ≤∞ ↑ 0 → a ≤∞ ↑ 0
+∞-≤∞-0ˡ {↑ x} {↑ _} p = m+n≤o⇒m≤o x p
+∞-≤∞-0ˡ {↑ _} {∞}   ()
+∞-≤∞-0ˡ {∞}   {_}   ()

+∞-≤∞-0ʳ : ∀ {a b} → (a +∞ b) ≤∞ ↑ 0 → b ≤∞ ↑ 0
+∞-≤∞-0ʳ {↑ x} {↑ _} p = m+n≤o⇒n≤o x p
+∞-≤∞-0ʳ {↑ _} {∞}   ()
+∞-≤∞-0ʳ {∞}   {_}   ()

-- a finite sum that is ↑ 0 forces both summands to be ↑ 0

+∞-≡0ˡ : ∀ {a b} → (a +∞ b) ≡ ↑ 0 → a ≡ ↑ 0
+∞-≡0ˡ {↑ x} {↑ _} eq = cong ↑_ (m+n≡0⇒m≡0 x (↑-inj eq))
+∞-≡0ˡ {↑ _} {∞}   ()
+∞-≡0ˡ {∞}   {_}   ()

+∞-≡0ʳ : ∀ {a b} → (a +∞ b) ≡ ↑ 0 → b ≡ ↑ 0
+∞-≡0ʳ {↑ x} {↑ _} eq = cong ↑_ (m+n≡0⇒n≡0 x (↑-inj eq))
+∞-≡0ʳ {↑ _} {∞}   ()
+∞-≡0ʳ {∞}   {_}   ()

-- anything below ↑ 0 is ↑ 0

≤∞-↑0 : ∀ {a} → a ≤∞ ↑ 0 → a ≡ ↑ 0
≤∞-↑0 {↑ _} p = cong ↑_ (n≤0⇒n≡0 p)
≤∞-↑0 {∞}   ()

------------------------------------------------------------------------
-- The closure under addition: `0` absorbs its own iteration, and of the
-- other values only `∞` does

plus∞ : ℕ∞ → ℕ∞
plus∞ (↑ zero)  = ↑ zero
plus∞ (↑ suc _) = ∞
plus∞ ∞         = ∞

≤∞-plus∞ : ∀ a → a ≤∞ plus∞ a
≤∞-plus∞ (↑ zero)  = ≤-refl
≤∞-plus∞ (↑ suc _) = tt
≤∞-plus∞ ∞         = tt

plus∞-iter : ∀ a → (plus∞ a +∞ plus∞ a) ≤∞ plus∞ a
plus∞-iter (↑ zero)  = ≤-refl
plus∞-iter (↑ suc _) = tt
plus∞-iter ∞         = tt

-- a finite value absorbing its own iteration is zero

+∞-self : ∀ {n} → (↑ n +∞ ↑ n) ≤∞ ↑ n → n ≡ 0
+∞-self {n} p = n≤0⇒n≡0 (+-cancelˡ-≤ n n 0 (subst (n + n ≤_) (sym (+-identityʳ n)) p))

plus∞-least : ∀ {a v} → a ≤∞ v → (v +∞ v) ≤∞ v → plus∞ a ≤∞ v
plus∞-least {↑ zero}  {↑ _} p q = z≤n
plus∞-least {↑ zero}  {∞}   p q = tt
plus∞-least {↑ suc n} {↑ m} p q with +∞-self {m} q
plus∞-least {↑ suc n} {↑ m} () q | refl
plus∞-least {↑ suc n} {∞}   p q = tt
plus∞-least {∞}       {∞}   p q = tt

-- a value that a summand does not move, the summand's closure does not
-- move either

plus∞-indˡ : ∀ {a b} → (a +∞ b) ≤∞ b → (plus∞ a +∞ b) ≤∞ b
plus∞-indˡ {↑ zero}  {b}   p = p
plus∞-indˡ {↑ suc n} {↑ m} p = ⊥-elim (<-irrefl refl (≤-trans p (m≤n+m m n)))
plus∞-indˡ {↑ suc n} {∞}   p = tt
plus∞-indˡ {∞}       {↑ _} ()
plus∞-indˡ {∞}       {∞}   p = tt

plus∞-indʳ : ∀ {a b} → (b +∞ a) ≤∞ b → (b +∞ plus∞ a) ≤∞ b
plus∞-indʳ {a} {b} p =
  subst (_≤∞ b) (+∞-comm (plus∞ a) b) (plus∞-indˡ (subst (_≤∞ b) (+∞-comm b a) p))
