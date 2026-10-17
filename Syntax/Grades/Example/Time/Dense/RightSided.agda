------------------------------------------------------------------------
-- (Right) one-sided (closed) intervals of dense time as grades.      --
--                                                                    --
-- A grade `[0, q ]` is an upper bound, "at most `q` time units",     --
-- with `q` a possibly infinite non-negative rational; a deadline of  --
-- 2.5 units is `[0, ↑ 5 / 2 ]`. Multiplication adds the bounds and   --
-- the order is `≤` on them, and a *larger* bound is the weaker       --
-- grade; `[0, ∞ ]` imposes no deadline and is absorbing. Durations   --
-- are non-negative rationals, a delay by `q` having grade            --
-- `[0, ↑ q ]`.                                                       --
--                                                                    --
-- The discrete intervals of `Time.RightSided` embed along the        --
-- inclusion of durations, a deadline of `n` time steps being read as --
-- one of `n` units of dense time.                                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Time.Dense.RightSided where

open import Data.List.Base using (List; []; _∷_) renaming (map to mapᴸ)
open import Data.Nat.Base using (ℕ)
open import Data.Product

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Data.Maybe.Base using (just)

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℕ→ℚ≥0ᴰ)
open import Syntax.Grades

open import Util.Equality

-- the endpoint is an extended non-negative rational

open import Syntax.Grades.Example.Time.Dense.ExtendedRational public

import Syntax.Grades.Example.Time.RightSided as Discrete

-- type of one-sided intervals

data 𝕀ᵣ : Set where
  [0,_] : ℚ∞ → 𝕀ᵣ

-- equality helpers

eq𝕀ᵣ : ∀ {a b} → a ≡ b → [0, a ] ≡ [0, b ]
eq𝕀ᵣ = cong [0,_]

𝕀ᵣ-inj : ∀ {a b} → [0, a ] ≡ [0, b ] → a ≡ b
𝕀ᵣ-inj refl = refl

-- interval addition

_·ₒ_ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ
[0, a ] ·ₒ [0, b ] = [0, a +∞ b ]

infixl 7 _·ₒ_

-- interval unit

uₒ : 𝕀ᵣ
uₒ = [0, ↑ 0ᵈ ]

-- interval order

_≾ₒ_ : Rel 𝕀ᵣ lzero
[0, a ] ≾ₒ [0, b ] = a ≤∞ b

infix 6 _≾ₒ_

-- the greatest grade: no deadline at all

⊤ₒ : 𝕀ᵣ
⊤ₒ = [0, ∞ ]

≾ₒ-⊤ : (i : 𝕀ᵣ) → i ≾ₒ ⊤ₒ
≾ₒ-⊤ [0, a ] = ≤∞-∞ a

-- the unit is least: no time at all meets every deadline

uₒ-least : Minimum _≾ₒ_ uₒ
uₒ-least [0, ↑ q ] = 0≤ q
uₒ-least [0, ∞ ]   = ≤∞-∞ ∞

-- identity laws

·ₒ-identityʳ : (i : 𝕀ᵣ) → i ·ₒ uₒ ≡ i
·ₒ-identityʳ [0, a ] = eq𝕀ᵣ (+∞-identityʳ a)

·ₒ-identityˡ : (i : 𝕀ᵣ) → uₒ ·ₒ i ≡ i
·ₒ-identityˡ [0, a ] = eq𝕀ᵣ (+∞-identityˡ a)

-- associativity

·ₒ-assoc : (i₁ i₂ i₃ : 𝕀ᵣ) → (i₁ ·ₒ i₂) ·ₒ i₃ ≡ i₁ ·ₒ (i₂ ·ₒ i₃)
·ₒ-assoc [0, a ] [0, b ] [0, c ] = eq𝕀ᵣ (+∞-assoc a b c)

-- commutativity

·ₒ-comm : (i₁ i₂ : 𝕀ᵣ) → i₁ ·ₒ i₂ ≡ i₂ ·ₒ i₁
·ₒ-comm [0, a ] [0, b ] = eq𝕀ᵣ (+∞-comm a b)

-- monotonicity

·ₒ-monoʳ-≾ₒ : ∀ {i} → (i ·ₒ_) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoʳ-≾ₒ {[0, a ]} {[0, x ]} {[0, y ]} rel =
  +∞-mono-≤∞ {a} {x} {a} {y} (≤∞-refl {a}) rel

·ₒ-monoˡ-≾ₒ : ∀ {i} → (_·ₒ i) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoˡ-≾ₒ {[0, a ]} {[0, x ]} {[0, y ]} rel =
  +∞-mono-≤∞ {x} {a} {y} {a} rel (≤∞-refl {a})

-- order properties

≾ₒ-refl : Reflexive _≾ₒ_
≾ₒ-refl {[0, a ]} = ≤∞-refl {a}

≾ₒ-trans : Transitive _≾ₒ_
≾ₒ-trans {[0, a ]} {[0, b ]} {[0, c ]} p q = ≤∞-trans {a} {b} {c} p q

≾ₒ-antisym : {i j : 𝕀ᵣ} → i ≾ₒ j → j ≾ₒ i → i ≡ j
≾ₒ-antisym {[0, a ]} {[0, b ]} p q = eq𝕀ᵣ (≤∞-antisym {a} {b} p q)

≾ₒ-irrelevant : Irrelevant _≾ₒ_
≾ₒ-irrelevant {[0, a ]} {[0, b ]} = ≤∞-irrelevant {a} {b}

-- decidability

_≾ₒ?_ : Decidable _≾ₒ_
[0, a ] ≾ₒ? [0, b ] = a ≤∞? b

-- zero-product properties

≡ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≡ uₒ → i₁ ≡ uₒ
≡ₒ-zero-productˡ {[0, a ]} {[0, b ]} eq =
  eq𝕀ᵣ (≤∞-↑0 (+∞-≤∞-0ˡ {a} {b} (≤∞-reflexive (𝕀ᵣ-inj eq))))

≡ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≡ uₒ → i₂ ≡ uₒ
≡ₒ-zero-productʳ {[0, a ]} {[0, b ]} eq =
  eq𝕀ᵣ (≤∞-↑0 (+∞-≤∞-0ʳ {a} {b} (≤∞-reflexive (𝕀ᵣ-inj eq))))

≾ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₁ ≾ₒ uₒ
≾ₒ-zero-productˡ {[0, a ]} {[0, b ]} rel = +∞-≤∞-0ˡ {a} {b} rel

≾ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀ᵣ} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₂ ≾ₒ uₒ
≾ₒ-zero-productʳ {[0, a ]} {[0, b ]} rel = +∞-≤∞-0ʳ {a} {b} rel

-- binary joins: a weaker grade has the larger deadline, so the join
-- takes the maximum of the two endpoints

_⊔ₒ_ : 𝕀ᵣ → 𝕀ᵣ → 𝕀ᵣ
[0, a ] ⊔ₒ [0, b ] = [0, a ⊔∞ b ]

infixl 7 _⊔ₒ_

⊔ₒ-ubˡ : (i₁ i₂ : 𝕀ᵣ) → i₁ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubˡ [0, a ] [0, b ] = ⊔∞-ubˡ a b

⊔ₒ-ubʳ : (i₁ i₂ : 𝕀ᵣ) → i₂ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubʳ [0, a ] [0, b ] = ⊔∞-ubʳ a b

⊔ₒ-lub : {i₁ i₂ i₃ : 𝕀ᵣ} → i₁ ≾ₒ i₃ → i₂ ≾ₒ i₃ → i₁ ⊔ₒ i₂ ≾ₒ i₃
⊔ₒ-lub {[0, a ]} {[0, b ]} {[0, c ]} p q = ⊔∞-lub {a} {b} {c} p q

-- addition distributes over the join, so the two sides are equal

·ₒ-distribˡ-⊔ₒ : (i₁ i₂ i₃ : 𝕀ᵣ) → i₁ ·ₒ (i₂ ⊔ₒ i₃) ≾ₒ (i₁ ·ₒ i₂) ⊔ₒ (i₁ ·ₒ i₃)
·ₒ-distribˡ-⊔ₒ [0, a ] [0, b ] [0, c ] = ≤∞-reflexive (+∞-distribˡ-⊔∞ a b c)

·ₒ-distribʳ-⊔ₒ : (i₁ i₂ i₃ : 𝕀ᵣ) → (i₂ ⊔ₒ i₃) ·ₒ i₁ ≾ₒ (i₂ ·ₒ i₁) ⊔ₒ (i₃ ·ₒ i₁)
·ₒ-distribʳ-⊔ₒ [0, a ] [0, b ] [0, c ] = ≤∞-reflexive (+∞-distribʳ-⊔∞ a b c)

-- the grade of (right) one-sided intervals of dense time

-- the closure: no time absorbs its own iteration, and of the other
-- bounds only the absent one does

plusₒ : (i : 𝕀ᵣ) → Plus _·ₒ_ _≾ₒ_ i
plusₒ [0, a ] = plus [0, plus∞ a ] (≤∞-plus∞ a) (plus∞-iter a) (λ {v} → least v)
                     (λ {d} → indˡ d) (λ {d} → indʳ d)
  where
    least : ∀ v → [0, a ] ≾ₒ v → v ·ₒ v ≾ₒ v → [0, plus∞ a ] ≾ₒ v
    least [0, b ] = plus∞-least

    indˡ : ∀ d → [0, a ] ·ₒ d ≾ₒ d → [0, plus∞ a ] ·ₒ d ≾ₒ d
    indˡ [0, b ] = plus∞-indˡ

    indʳ : ∀ d → d ·ₒ [0, a ] ≾ₒ d → d ·ₒ [0, plus∞ a ] ≾ₒ d
    indʳ [0, b ] = plus∞-indʳ

dense-right-sided-intervals : Grade ℚ≥0ᴰ
dense-right-sided-intervals = record
  { Carrier           = 𝕀ᵣ
  ; _·_               = _·ₒ_
  ; u                 = uₒ
  ; ·-identityʳ       = ·ₒ-identityʳ
  ; ·-identityˡ       = ·ₒ-identityˡ
  ; ·-assoc           = ·ₒ-assoc
  ; _≾_               = _≾ₒ_
  ; ⊤                 = ⊤ₒ
  ; ≾-⊤               = ≾ₒ-⊤
  ; u-least?          = just uₒ-least
  ; ·-comm?           = just ·ₒ-comm
  ; plus?             = λ i → just (plusₒ i)
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
  ; of-dur            = λ q → [0, ↑ q ]
  ; of-dur-zero       = refl
  ; of-dur-plus       = refl
  }

------------------------------------------------------------------------
-- The discrete intervals embed

right-sided→dense : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.right-sided-intervals
                                         dense-right-sided-intervals
right-sided→dense = record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-u        = refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-of-dur   = refl
  }
  where
    embed : Discrete.𝕀ᵣ → 𝕀ᵣ
    embed Discrete.[0, a ] = [0, ℕ∞→ℚ∞ a ]

    mono : ∀ {i j} → i Discrete.≾ₒ j → embed i ≾ₒ embed j
    mono {Discrete.[0, a ]} {Discrete.[0, b ]} = ℕ∞→ℚ∞-mono {a} {b}

    hom : ∀ {i j} → embed (i Discrete.·ₒ j) ≡ embed i ·ₒ embed j
    hom {Discrete.[0, a ]} {Discrete.[0, b ]} = eq𝕀ᵣ (ℕ∞→ℚ∞-+ a b)

    join : ∀ {i j} → embed (i Discrete.⊔ₒ j) ≡ embed i ⊔ₒ embed j
    join {Discrete.[0, a ]} {Discrete.[0, b ]} = eq𝕀ᵣ (ℕ∞→ℚ∞-⊔ a b)

------------------------------------------------------------------------
-- Candidate grades for a rigid: the bounds of the grid of the finite
-- constants (`grid`)

dense-right-sided-witnesses : ℕ → List 𝕀ᵣ → List 𝕀ᵣ
dense-right-sided-witnesses d cs = mapᴸ (λ q → [0, ↑ q ]) (grid d (finite cs))
  where
    finite : List 𝕀ᵣ → List ℚ≥0
    finite []                = []
    finite ([0, ↑ q ] ∷ cs') = q ∷ finite cs'
    finite ([0, ∞ ] ∷ cs')   = finite cs'
