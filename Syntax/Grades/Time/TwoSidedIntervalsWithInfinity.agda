-----------------------------------------------------------
-- Two-sided (closed) intervals with a possibly-infinite --
-- right-hand endpoint as grades                         --
-----------------------------------------------------------

module Syntax.Grades.Time.TwoSidedIntervalsWithInfinity where

open import Data.Empty
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Syntax.Grades

open import Util.Equality

--------------------------
-- Extended naturals ℕ∞ --
--------------------------

-- `↑ n` is the finite value `n`, while `∞` is the point at infinity.

data ℕ∞ : Set₀ where
  ↑_ : ℕ → ℕ∞
  ∞  : ℕ∞

infix 8 ↑_

↑-inj : ∀ {m n} → ↑ m ≡ ↑ n → m ≡ n
↑-inj refl = refl

-- addition (∞ is absorbing)

_+∞_ : ℕ∞ → ℕ∞ → ℕ∞
↑ m +∞ ↑ n = ↑ (m + n)
↑ m +∞ ∞   = ∞
∞   +∞ _   = ∞

infixl 7 _+∞_

-- order (everything is below ∞)

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

-- order is reflexive and transitive

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

-- decidable equality

_≟∞_ : Decidable {A = ℕ∞} _≡_
(↑ m) ≟∞ (↑ n) with m ≟ n
... | yes p = yes (cong ↑_ p)
... | no ¬p = no λ eq → ¬p (↑-inj eq)
(↑ _) ≟∞ ∞     = no λ ()
∞     ≟∞ (↑ _) = no λ ()
∞     ≟∞ ∞     = yes refl

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

----------------------------------
-- Intervals with infinite max --
----------------------------------

record Interval∞ : Set₀ where
  constructor [_,_,_]
  field
    min : ℕ
    max : ℕ∞
    -- min is smaller or equal than max
    min≤max : ↑ min ≤∞ max

open Interval∞ public

-- interval addition

_·ᵢ_ : Interval∞ → Interval∞ → Interval∞
i₁ ·ᵢ i₂ =
  [ min i₁ + min i₂
  , max i₁ +∞ max i₂
  , +∞-mono-≤∞ {↑ min i₁} {↑ min i₂} {max i₁} {max i₂} (min≤max i₁) (min≤max i₂)
  ]

infixl 7 _·ᵢ_

-- interval unit

uᵢ : Interval∞
uᵢ = [ 0 , ↑ 0 , z≤n ]

-- interval equality

eqᵢ : ∀ {i₁ i₂}
    → min i₁ ≡ min i₂
    → max i₁ ≡ max i₂
    -----------------
    → i₁ ≡ i₂

eqᵢ {_} {i₂} refl refl =
  cong (λ x → [ min i₂ , max i₂ , x ]) (≤∞-irrelevant _ _)

-- right and left identity

·ᵢ-identityʳ : (i : Interval∞) → (i ·ᵢ uᵢ) ≡ i
·ᵢ-identityʳ i =
  eqᵢ (+-identityʳ (min i)) (+∞-identityʳ (max i))

·ᵢ-identityˡ : (i : Interval∞) → (uᵢ ·ᵢ i) ≡ i
·ᵢ-identityˡ i =
  eqᵢ (+-identityˡ (min i)) (+∞-identityˡ (max i))

-- _·ᵢ_ is associative

·ᵢ-assoc : (i₁ i₂ i₃ : Interval∞) → (i₁ ·ᵢ i₂) ·ᵢ i₃ ≡ i₁ ·ᵢ (i₂ ·ᵢ i₃)
·ᵢ-assoc i₁ i₂ i₃ =
  eqᵢ
    (+-assoc (min i₁) (min i₂) (min i₃))
    (+∞-assoc (max i₁) (max i₂) (max i₃))

-- interval order

_≾ᵢ_ : Rel Interval∞ lzero
i₁ ≾ᵢ i₂ =
  (min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂)

-- uᵢ is the minimal element

uᵢ-minimal : ∀ {i} → i ≾ᵢ uᵢ → i ≡ uᵢ
uᵢ-minimal {i} (_ , maxrel) =
  eqᵢ {i} {uᵢ}
    (n≤0⇒n≡0 (≤∞-trans {↑ min i} (min≤max i) maxrel))
    (≤∞-↑0 maxrel)

-- monotonicity

·ᵢ-monoʳ-≾ᵢ : ∀ {i} → _·ᵢ_ i Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoʳ-≤ (min i) {min i₂} {min i₁} minrel ,
  +∞-mono-≤∞ {max i} {max i₁} {max i} {max i₂} (≤∞-refl {max i}) maxrel

·ᵢ-monoˡ-≾ᵢ : ∀ {i} → (_·ᵢ i) Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoˡ-≤ (min i) {min i₂} {min i₁} minrel ,
  +∞-mono-≤∞ {max i₁} {max i} {max i₂} {max i} maxrel (≤∞-refl {max i})

-- irrelevance

≾ᵢ-irrelevant : Irrelevant _≾ᵢ_
≾ᵢ-irrelevant (relmin , relmax) (predmin , predmax) =
  cong₂ _,_ (≤-irrelevant relmin predmin) (≤∞-irrelevant relmax predmax)

-- decidability

eqᵢ? : Decidable {lzero} {Interval∞} _≡_
eqᵢ? i₁ i₂ with min i₁ ≟ min i₂ | max i₁ ≟∞ max i₂
... | yes p | yes q = yes (eqᵢ p q)
... | yes _ | no ¬q = no  λ x → ¬q (cong max x)
... | no ¬p | _     = no  λ x → ¬p (cong min x)

-- NB: unlike the all-finite two-sided intervals, _·ᵢ_ is *not*
-- cancellative once ∞ is allowed: e.g. with max i₁ = ∞ we have
-- (i₁ ·ᵢ i₂) ≾ᵢ (i₁ ·ᵢ i₃) for all i₂ i₃, yet i₂ ≾ᵢ i₃ may fail.

-- zero-product property

≡ᵢ-zero-productˡ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ uᵢ → i₁ ≡ uᵢ
≡ᵢ-zero-productˡ {i₁} {i₂} eq =
   eqᵢ
     (m+n≡0⇒m≡0 (min i₁) (cong min eq))
     (+∞-≡0ˡ {max i₁} {max i₂} (cong max eq))

≡ᵢ-zero-productʳ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ uᵢ → i₂ ≡ uᵢ
≡ᵢ-zero-productʳ {i₁} {i₂} eq =
  eqᵢ
    (m+n≡0⇒n≡0 (min i₁) {min i₂} (cong min eq))
    (+∞-≡0ʳ {max i₁} {max i₂} (cong max eq))

≾ᵢ-zero-productˡ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ uᵢ → i₁ ≾ᵢ uᵢ
≾ᵢ-zero-productˡ {i₁} {i₂} (_ , maxrel) =
  z≤n , +∞-≤∞-0ˡ {max i₁} {max i₂} maxrel

≾ᵢ-zero-productʳ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ uᵢ → i₂ ≾ᵢ uᵢ
≾ᵢ-zero-productʳ {i₁} {i₂} (_ , maxrel) =
  z≤n , +∞-≤∞-0ʳ {max i₁} {max i₂} maxrel

-- the grade of two-sided intervals with possibly-infinite max

two-sided-intervals-with-∞ : Grade
two-sided-intervals-with-∞ = record
  { Carrier = Interval∞
  ; _·_              = _·ᵢ_
  ; u                = uᵢ
  ; ·-identityʳ      = ·ᵢ-identityʳ
  ; ·-identityˡ      = ·ᵢ-identityˡ
  ; ·-assoc          = ·ᵢ-assoc
  ; _≾_              = _≾ᵢ_
  ; ·-monoʳ-≾        = λ {i} {i₁} {i₂} rel
                         → ·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} rel
  ; ·-monoˡ-≾        = λ {i} {i₁} {i₂} rel
                         → ·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} rel
  ; ≾-refl           = ≤-refl , ≤∞-refl
  ; ≾-trans          = λ rel₁ rel₂
                         → ≤-trans (proj₁ rel₂) (proj₁ rel₁) ,
                           ≤∞-trans (proj₂ rel₁) (proj₂ rel₂)
  ; _≡?_              = eqᵢ?
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ᵢ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ᵢ-zero-productʳ {i₁} {i₂}
  ; of-nat            = λ n → [ n , ↑ n , ≤-refl ]
  ; of-nat-zero       = eqᵢ refl refl
  ; of-nat-plus       = eqᵢ refl refl
  }
