------------------------------------------------------------------------
-- (Right) one-sided (closed) intervals as grades.                     --
--                                                                     --
-- A grade `[0, n ]` is an upper bound: "at most `n` time steps", with  --
-- `n` a possibly-infinite natural. Multiplication adds the bounds and  --
-- the order is `≤` on them, so a *larger* bound is the weaker grade -- --
-- the mirror image of the left-sided intervals.                        --
--                                                                     --
-- The endpoint is extended because `ℕ` has no greatest element and a   --
-- deadline grade needs one: `[0, ∞ ]` imposes no deadline at all, and  --
-- is absorbing, a computation after an unbounded one still being       --
-- unbounded. The arithmetic lives in `Time.ExtendedNat` and is         --
-- re-exported here.                                                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Time.RightSided where

open import Data.Nat
open import Data.Nat.Properties
open import Data.Product

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Data.Maybe.Base using (just)

open import Syntax.Grades

open import Util.Equality

-- the endpoint is an extended natural

open import Syntax.Grades.Example.Time.ExtendedNat public

-- type of one-sided intervals

data 𝕀ᵣ : Set where
  [0,_] : ℕ∞ → 𝕀ᵣ

-- equality helpers

eq𝕀ᵣ : ∀ {m n} → m ≡ n → [0, m ] ≡ [0, n ]
eq𝕀ᵣ = cong [0,_]

𝕀ᵣ-inj : ∀ {m n} → [0, m ] ≡ [0, n ] → m ≡ n
𝕀ᵣ-inj refl = refl

-- interval addition

_·ₒ_ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ
[0, m ] ·ₒ [0, n ] = [0, m +∞ n ]

infixl 7 _·ₒ_

-- interval unit

uₒ : 𝕀ᵣ
uₒ = [0, ↑ 0 ]

-- interval order

_≾ₒ_ : Rel 𝕀ᵣ lzero
[0, m ] ≾ₒ [0, n ] = m ≤∞ n

infix 6 _≾ₒ_

-- the greatest grade: no deadline at all

⊤ₒ : 𝕀ᵣ
⊤ₒ = [0, ∞ ]

≾ₒ-⊤ : (i : 𝕀ᵣ) → i ≾ₒ ⊤ₒ
≾ₒ-⊤ [0, m ] = ≤∞-∞ m

-- the unit is least: no time at all meets every deadline

uₒ-least : Minimum _≾ₒ_ uₒ
uₒ-least [0, ↑ _ ] = z≤n
uₒ-least [0, ∞ ]   = ≤∞-∞ ∞

-- identity laws

·ₒ-identityʳ : (i : 𝕀ᵣ) → i ·ₒ uₒ ≡ i
·ₒ-identityʳ [0, m ] = eq𝕀ᵣ (+∞-identityʳ m)

·ₒ-identityˡ : (i : 𝕀ᵣ) → uₒ ·ₒ i ≡ i
·ₒ-identityˡ [0, m ] = eq𝕀ᵣ (+∞-identityˡ m)

-- associativity

·ₒ-assoc : (i₁ i₂ i₃ : 𝕀ᵣ) → (i₁ ·ₒ i₂) ·ₒ i₃ ≡ i₁ ·ₒ (i₂ ·ₒ i₃)
·ₒ-assoc [0, m ] [0, n ] [0, o ] = eq𝕀ᵣ (+∞-assoc m n o)

-- commutativity

·ₒ-comm : (i₁ i₂ : 𝕀ᵣ) → i₁ ·ₒ i₂ ≡ i₂ ·ₒ i₁
·ₒ-comm [0, m ] [0, n ] = eq𝕀ᵣ (+∞-comm m n)

-- monotonicity

·ₒ-monoʳ-≾ₒ : ∀ {i} → (i ·ₒ_) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoʳ-≾ₒ {[0, m ]} {[0, x ]} {[0, y ]} rel =
  +∞-mono-≤∞ {m} {x} {m} {y} (≤∞-refl {m}) rel

·ₒ-monoˡ-≾ₒ : ∀ {i} → (_·ₒ i) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoˡ-≾ₒ {[0, m ]} {[0, x ]} {[0, y ]} rel =
  +∞-mono-≤∞ {x} {m} {y} {m} rel (≤∞-refl {m})

-- order properties

≾ₒ-refl : Reflexive _≾ₒ_
≾ₒ-refl {[0, m ]} = ≤∞-refl {m}

≾ₒ-trans : Transitive _≾ₒ_
≾ₒ-trans {[0, m ]} {[0, n ]} {[0, o ]} p q = ≤∞-trans {m} {n} {o} p q

≾ₒ-antisym : {i j : 𝕀ᵣ} → i ≾ₒ j → j ≾ₒ i → i ≡ j
≾ₒ-antisym {[0, m ]} {[0, n ]} p q = eq𝕀ᵣ (≤∞-antisym {m} {n} p q)

≾ₒ-irrelevant : Irrelevant _≾ₒ_
≾ₒ-irrelevant {[0, m ]} {[0, n ]} = ≤∞-irrelevant {m} {n}

-- decidability

_≾ₒ?_ : Decidable _≾ₒ_
[0, m ] ≾ₒ? [0, n ] = m ≤∞? n

-- Unlike the all-finite deadlines, _·ₒ_ is *not* cancellative once ∞
-- is allowed.

-- zero-product properties

≡ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≡ uₒ → i₁ ≡ uₒ
≡ₒ-zero-productˡ {[0, m ]} {[0, n ]} eq = eq𝕀ᵣ (+∞-≡0ˡ {m} {n} (𝕀ᵣ-inj eq))

≡ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≡ uₒ → i₂ ≡ uₒ
≡ₒ-zero-productʳ {[0, m ]} {[0, n ]} eq = eq𝕀ᵣ (+∞-≡0ʳ {m} {n} (𝕀ᵣ-inj eq))

≾ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₁ ≾ₒ uₒ
≾ₒ-zero-productˡ {[0, m ]} {[0, n ]} rel = +∞-≤∞-0ˡ {m} {n} rel

≾ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₂ ≾ₒ uₒ
≾ₒ-zero-productʳ {[0, m ]} {[0, n ]} rel = +∞-≤∞-0ʳ {m} {n} rel

-- binary joins: a weaker grade has the larger deadline, so the join
-- takes the maximum of the two endpoints

_⊔ₒ_ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ
[0, m ] ⊔ₒ [0, n ] = [0, m ⊔∞ n ]

infixl 7 _⊔ₒ_

⊔ₒ-ubˡ : (i₁ i₂ : 𝕀ᵣ) → i₁ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubˡ [0, m ] [0, n ] = ⊔∞-ubˡ m n

⊔ₒ-ubʳ : (i₁ i₂ : 𝕀ᵣ) → i₂ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubʳ [0, m ] [0, n ] = ⊔∞-ubʳ m n

⊔ₒ-lub : {i₁ i₂ i₃ : 𝕀ᵣ} → i₁ ≾ₒ i₃ → i₂ ≾ₒ i₃ → i₁ ⊔ₒ i₂ ≾ₒ i₃
⊔ₒ-lub {[0, m ]} {[0, n ]} {[0, o ]} p q = ⊔∞-lub {m} {n} {o} p q

-- addition distributes over the join, so the two sides are equal

·ₒ-distribˡ-⊔ₒ : (i₁ i₂ i₃ : 𝕀ᵣ) → i₁ ·ₒ (i₂ ⊔ₒ i₃) ≾ₒ (i₁ ·ₒ i₂) ⊔ₒ (i₁ ·ₒ i₃)
·ₒ-distribˡ-⊔ₒ [0, m ] [0, n ] [0, o ] = ≤∞-reflexive (+∞-distribˡ-⊔∞ m n o)

·ₒ-distribʳ-⊔ₒ : (i₁ i₂ i₃ : 𝕀ᵣ) → (i₂ ⊔ₒ i₃) ·ₒ i₁ ≾ₒ (i₂ ·ₒ i₁) ⊔ₒ (i₃ ·ₒ i₁)
·ₒ-distribʳ-⊔ₒ [0, m ] [0, n ] [0, o ] = ≤∞-reflexive (+∞-distribʳ-⊔∞ m n o)

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
  ; ⊤                 = ⊤ₒ
  ; ≾-⊤               = ≾ₒ-⊤
  ; u-least?          = yes uₒ-least
  ; ·-comm?           = just ·ₒ-comm
  ; _⊔_               = _⊔ₒ_
  ; ⊔-ubˡ             = ⊔ₒ-ubˡ
  ; ⊔-ubʳ             = ⊔ₒ-ubʳ
  ; ⊔-lub             = λ {i₁} {i₂} {i₃} → ⊔ₒ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾    = ·ₒ-distribˡ-⊔ₒ
  ; ·-distribʳ-⊔-≾    = ·ₒ-distribʳ-⊔ₒ
  ; ·-monoʳ-≾         = λ {i} {i₁} {i₂} → ·ₒ-monoʳ-≾ₒ {i} {i₁} {i₂}
  ; ·-monoˡ-≾         = λ {i} {i₁} {i₂} → ·ₒ-monoˡ-≾ₒ {i} {i₁} {i₂}
  ; ≾-refl            = λ {i} → ≾ₒ-refl {i}
  ; ≾-trans           = λ {i₁} {i₂} {i₃} → ≾ₒ-trans {i₁} {i₂} {i₃}
  ; ≾-antisym         = λ {i₁} {i₂} → ≾ₒ-antisym {i₁} {i₂}
  ; _≾?_              = _≾ₒ?_
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ₒ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ₒ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ₒ-irrelevant {i₁} {i₂}
  ; of-nat            = λ n → [0, ↑ n ]
  ; of-nat-zero       = refl
  ; of-nat-plus       = refl
  }
