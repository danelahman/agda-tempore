------------------------------------------------------------------------
-- Closed two-sided intervals of dense time, with a possibly infinite --
-- right-hand endpoint, as grades.                                    --
--                                                                    --
-- A grade `[ min , max ]` bounds the elapsed time from both sides,   --
-- "between `min` and `max` time units" inclusive, `min` a            --
-- non-negative rational and `max` an extended one, `∞` imposing no   --
-- upper bound. The order is containment, and a wider window is the   --
-- weaker grade; a delay by `q` has grade `[ q , ↑ q ]`.              --
--                                                                    --
-- These are the intervals of `Time.Dense.TwoSided` whose ends are    --
-- closed, and they embed there by a grade morphism. The discrete     --
-- windows of `Time.TwoSidedWithInfinity` embed here along the        --
-- inclusion of durations, a window of time steps being read as the   --
-- same window of dense time.                                         --
------------------------------------------------------------------------

module Grades.Examples.Time.Dense.TwoSidedClosed where

open import Data.Bool.Properties using (T-irrelevant)
open import Data.Product
open import Data.Unit using (tt)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation.Core using (¬_)

open import Data.Maybe.Base using (just; nothing)

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℕ→ℚ≥0ᴰ)
open import Grades.Base
open import Grades.Hints using (GradeHints; comm-≡)

open import Util.Equality

-- the endpoints are (extended) non-negative rationals

open import Grades.Examples.Time.Dense.ExtendedRational public

import Grades.Examples.Time.TwoSidedWithInfinity as Discrete

------------------------------------------------------------------------
-- Intervals with infinite max
--
-- The side condition is the verdict of `_≤∞?_`, so at concrete
-- endpoints it reduces to `⊤` and a literal is written `[ p , a ]`.

record Interval∞ : Set₀ where
  constructor [_,_]
  field
    min : ℚ≥0
    max : ℚ∞
    -- min is at most max
    {min≤max?} : True (↑ min ≤∞? max)

open Interval∞ public

-- the side condition, as a proof

min≤max : (i : Interval∞) → ↑ min i ≤∞ max i
min≤max i = toWitness {a? = ↑ min i ≤∞? max i} (min≤max? i)

-- interval addition

_·ᵢ_ : Interval∞ → Interval∞ → Interval∞
i₁ ·ᵢ i₂ =
  [ min i₁ + min i₂
  , max i₁ +∞ max i₂
  ] {fromWitness (+∞-mono-≤∞ {↑ min i₁} {↑ min i₂} {max i₁} {max i₂}
                              (min≤max i₁) (min≤max i₂))}

infixl 7 _·ᵢ_

-- interval unit

𝟏ᵢ : Interval∞
𝟏ᵢ = [ 0ᵈ , ↑ 0ᵈ ]

-- interval equality

eqᵢ : ∀ {i₁ i₂}
    → min i₁ ≡ min i₂
    → max i₁ ≡ max i₂
    -----------------
    → i₁ ≡ i₂

eqᵢ {_} {i₂} refl refl =
  cong (λ x → [ min i₂ , max i₂ ] {x}) (T-irrelevant _ _)

-- right and left identity

·ᵢ-identityʳ : (i : Interval∞) → (i ·ᵢ 𝟏ᵢ) ≡ i
·ᵢ-identityʳ i =
  eqᵢ (+-identityʳ (min i)) (+∞-identityʳ (max i))

·ᵢ-identityˡ : (i : Interval∞) → (𝟏ᵢ ·ᵢ i) ≡ i
·ᵢ-identityˡ i =
  eqᵢ (+-identityˡ (min i)) (+∞-identityˡ (max i))

-- _·ᵢ_ is associative

·ᵢ-assoc : (i₁ i₂ i₃ : Interval∞) → (i₁ ·ᵢ i₂) ·ᵢ i₃ ≡ i₁ ·ᵢ (i₂ ·ᵢ i₃)
·ᵢ-assoc i₁ i₂ i₃ =
  eqᵢ
    (+-assoc (min i₁) (min i₂) (min i₃))
    (+∞-assoc (max i₁) (max i₂) (max i₃))

-- _·ᵢ_ is commutative

·ᵢ-comm : (i₁ i₂ : Interval∞) → i₁ ·ᵢ i₂ ≡ i₂ ·ᵢ i₁
·ᵢ-comm i₁ i₂ = eqᵢ (+-comm (min i₁) (min i₂)) (+∞-comm (max i₁) (max i₂))

-- interval order

_≾ᵢ_ : Rel Interval∞ lzero
i₁ ≾ᵢ i₂ =
  (min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂)

-- the greatest grade: no lower bound and no upper bound. It is not
-- absorbing, `⊤ᵢ ·ᵢ i` keeping `min i`.

⊤ᵢ : Interval∞
⊤ᵢ = [ 0ᵈ , ∞ ]

≾ᵢ-⊤ : (i : Interval∞) → (min ⊤ᵢ ≤ min i × max i ≤∞ max ⊤ᵢ)
≾ᵢ-⊤ i = 0≤ (min i) , ≤∞-∞ (max i)

-- the unit is not least: `[ 1 / 2 , ↑ 1 / 2 ]` is not above it, its
-- lower bound being higher

𝟏ᵢ-not-least : ¬ Minimum _≾ᵢ_ 𝟏ᵢ
𝟏ᵢ-not-least least =
  toWitnessFalse {a? = 1 / 2 ≤? 0ᵈ} tt (proj₁ (least [ 1 / 2 , ↑ 1 / 2 ]))

-- 𝟏ᵢ is the minimal element

𝟏ᵢ-minimal : ∀ {i} → i ≾ᵢ 𝟏ᵢ → i ≡ 𝟏ᵢ
𝟏ᵢ-minimal {i} (_ , maxrel) =
  eqᵢ {i} {𝟏ᵢ}
    (≤0⇒≡0 (≤∞-trans {↑ min i} {max i} {↑ 0ᵈ} (min≤max i) maxrel))
    (≤∞-↑0 maxrel)

-- monotonicity

·ᵢ-monoʳ-≾ᵢ : ∀ {i} → _·ᵢ_ i Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoʳ-≤ (min i) minrel ,
  +∞-mono-≤∞ {max i} {max i₁} {max i} {max i₂} (≤∞-refl {max i}) maxrel

·ᵢ-monoˡ-≾ᵢ : ∀ {i} → (_·ᵢ i) Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoˡ-≤ (min i) minrel ,
  +∞-mono-≤∞ {max i₁} {max i} {max i₂} {max i} maxrel (≤∞-refl {max i})

-- antisymmetry: both endpoints are pinned, and `eqᵢ` discharges the
-- `min≤max?` field

≾ᵢ-antisym : {i₁ i₂ : Interval∞} → i₁ ≾ᵢ i₂ → i₂ ≾ᵢ i₁ → i₁ ≡ i₂
≾ᵢ-antisym {i₁} {i₂} (min₂≤min₁ , max₁≤max₂) (min₁≤min₂ , max₂≤max₁) =
  eqᵢ {i₁} {i₂}
    (≤-antisym min₁≤min₂ min₂≤min₁)
    (≤∞-antisym {max i₁} {max i₂} max₁≤max₂ max₂≤max₁)

-- irrelevance

≾ᵢ-irrelevant : Irrelevant _≾ᵢ_
≾ᵢ-irrelevant {i₁} {i₂} (relmin , relmax) (predmin , predmax) =
  cong₂ _,_ (≤-irrelevant relmin predmin)
            (≤∞-irrelevant {max i₁} {max i₂} relmax predmax)

-- decidability

_≾ᵢ?_ : Decidable _≾ᵢ_
i₁ ≾ᵢ? i₂ with min i₂ ≤? min i₁ | max i₁ ≤∞? max i₂
... | yes p | yes q = yes (p , q)
... | yes _ | no ¬q = no λ r → ¬q (proj₂ r)
... | no ¬p | _     = no λ r → ¬p (proj₁ r)

-- zero-product property

≡ᵢ-zero-productˡ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ 𝟏ᵢ → i₁ ≡ 𝟏ᵢ
≡ᵢ-zero-productˡ {i₁} {i₂} eq =
  𝟏ᵢ-minimal {i₁} (0≤ (min i₁) ,
                   +∞-≤∞-0ˡ {max i₁} {max i₂} (≤∞-reflexive (cong max eq)))

≡ᵢ-zero-productʳ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ 𝟏ᵢ → i₂ ≡ 𝟏ᵢ
≡ᵢ-zero-productʳ {i₁} {i₂} eq =
  𝟏ᵢ-minimal {i₂} (0≤ (min i₂) ,
                   +∞-≤∞-0ʳ {max i₁} {max i₂} (≤∞-reflexive (cong max eq)))

≾ᵢ-zero-productˡ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ 𝟏ᵢ → i₁ ≾ᵢ 𝟏ᵢ
≾ᵢ-zero-productˡ {i₁} {i₂} (_ , maxrel) =
  0≤ (min i₁) , +∞-≤∞-0ˡ {max i₁} {max i₂} maxrel

≾ᵢ-zero-productʳ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ 𝟏ᵢ → i₂ ≾ᵢ 𝟏ᵢ
≾ᵢ-zero-productʳ {i₁} {i₂} (_ , maxrel) =
  0≤ (min i₂) , +∞-≤∞-0ʳ {max i₁} {max i₂} maxrel

-- binary joins: the order is containment, so the join is the smallest
-- window containing both

_⊔ᵢ_ : Interval∞ → Interval∞ → Interval∞
i₁ ⊔ᵢ i₂ =
  [ min i₁ ⊓ min i₂
  , max i₁ ⊔∞ max i₂
  ] {fromWitness
       (≤∞-trans {↑ (min i₁ ⊓ min i₂)} {↑ min i₁} {max i₁ ⊔∞ max i₂}
                 (⊓-lbˡ (min i₁) (min i₂))
                 (≤∞-trans {↑ min i₁} {max i₁} {max i₁ ⊔∞ max i₂}
                           (min≤max i₁) (⊔∞-ubˡ (max i₁) (max i₂))))}

infixl 7 _⊔ᵢ_

⊔ᵢ-ubˡ : (i₁ i₂ : Interval∞) → i₁ ≾ᵢ (i₁ ⊔ᵢ i₂)
⊔ᵢ-ubˡ i₁ i₂ = ⊓-lbˡ (min i₁) (min i₂) , ⊔∞-ubˡ (max i₁) (max i₂)

⊔ᵢ-ubʳ : (i₁ i₂ : Interval∞) → i₂ ≾ᵢ (i₁ ⊔ᵢ i₂)
⊔ᵢ-ubʳ i₁ i₂ = ⊓-lbʳ (min i₁) (min i₂) , ⊔∞-ubʳ (max i₁) (max i₂)

⊔ᵢ-lub : {i₁ i₂ i₃ : Interval∞} → i₁ ≾ᵢ i₃ → i₂ ≾ᵢ i₃ → (i₁ ⊔ᵢ i₂) ≾ᵢ i₃
⊔ᵢ-lub {i₁} {i₂} {i₃} (p₁ , p₂) (q₁ , q₂) =
  ⊓-glb p₁ q₁ , ⊔∞-lub {max i₁} {max i₂} {max i₃} p₂ q₂

-- addition distributes over the join at both endpoints, so the two
-- sides are equal

·ᵢ-distribˡ-⊔ᵢ : (i₁ i₂ i₃ : Interval∞)
               → (i₁ ·ᵢ (i₂ ⊔ᵢ i₃)) ≾ᵢ ((i₁ ·ᵢ i₂) ⊔ᵢ (i₁ ·ᵢ i₃))
·ᵢ-distribˡ-⊔ᵢ i₁ i₂ i₃ =
    ≤-reflexive (sym (+-distribˡ-⊓ (min i₁) (min i₂) (min i₃)))
  , ≤∞-reflexive (+∞-distribˡ-⊔∞ (max i₁) (max i₂) (max i₃))

·ᵢ-distribʳ-⊔ᵢ : (i₁ i₂ i₃ : Interval∞)
               → ((i₂ ⊔ᵢ i₃) ·ᵢ i₁) ≾ᵢ ((i₂ ·ᵢ i₁) ⊔ᵢ (i₃ ·ᵢ i₁))
·ᵢ-distribʳ-⊔ᵢ i₁ i₂ i₃ =
    ≤-reflexive (sym (+-distribʳ-⊓ (min i₁) (min i₂) (min i₃)))
  , ≤∞-reflexive (+∞-distribʳ-⊔∞ (max i₁) (max i₂) (max i₃))

-- the grade of closed two-sided intervals of dense time

-- the closure: the same lower bound, and an upper bound that only no
-- time or the absent bound absorbs

plusᵢ : (i : Interval∞) → Plus _·ᵢ_ _≾ᵢ_ i
plusᵢ i = plus i⁺ (≤-refl , ≤∞-plus∞ (max i))
               (p≤p+q (min i) (min i) , plus∞-iter (max i))
               (λ (p₁ , p₂) (_ , q₂) → p₁ , plus∞-least p₂ q₂)
               (λ (p₁ , p₂) → p₁ , plus∞-indˡ p₂) (λ (p₁ , p₂) → p₁ , plus∞-indʳ p₂)
  where
    i⁺ : Interval∞
    i⁺ = [ min i , plus∞ (max i) ]
           {fromWitness (≤∞-trans {↑ min i} {max i} (min≤max i) (≤∞-plus∞ (max i)))}

dense-closed-two-sided-intervals-with-∞ : Grade ℚ≥0ᴰ
dense-closed-two-sided-intervals-with-∞ = posetᵍ record
  { Carrier = Interval∞
  ; _·_              = _·ᵢ_
  ; 𝟏                = 𝟏ᵢ
  ; ·-identityʳ      = ·ᵢ-identityʳ
  ; ·-identityˡ      = ·ᵢ-identityˡ
  ; ·-assoc          = ·ᵢ-assoc
  ; _≾_              = _≾ᵢ_
  ; ⊤                = ⊤ᵢ
  ; ≾-⊤              = ≾ᵢ-⊤
  ; _⊔_              = _⊔ᵢ_
  ; ⊔-ubˡ            = ⊔ᵢ-ubˡ
  ; ⊔-ubʳ            = ⊔ᵢ-ubʳ
  ; ⊔-lub            = λ {i₁} {i₂} {i₃} → ⊔ᵢ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾   = ·ᵢ-distribˡ-⊔ᵢ
  ; ·-distribʳ-⊔-≾   = ·ᵢ-distribʳ-⊔ᵢ
  ; ·-monoʳ-≾        = λ {i} {i₁} {i₂} rel
                         → ·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} rel
  ; ·-monoˡ-≾        = λ {i} {i₁} {i₂} rel
                         → ·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} rel
  ; ≾-refl           = λ {i} → ≤-refl , ≤∞-refl {max i}
  ; ≾-trans          = λ {i₁} {i₂} {i₃} rel₁ rel₂
                         → ≤-trans (proj₁ rel₂) (proj₁ rel₁) ,
                           ≤∞-trans {max i₁} {max i₂} {max i₃}
                                    (proj₂ rel₁) (proj₂ rel₂)
  ; ≾-antisym        = λ {i₁} {i₂} → ≾ᵢ-antisym {i₁} {i₂}
  ; _≾?_              = _≾ᵢ?_
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ᵢ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ᵢ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ᵢ-irrelevant {i₁} {i₂}
  ; ι                 = λ q → [ q , ↑ q ] {fromWitness ≤-refl}
  ; ι-zero            = eqᵢ refl refl
  ; ι-plus            = eqᵢ refl refl
  }

-- its hints

dense-closed-two-sided-intervals-with-∞ʰ : GradeHints dense-closed-two-sided-intervals-with-∞
dense-closed-two-sided-intervals-with-∞ʰ = record
  { 𝟏-least? = nothing
  ; ·-comm?  = just (comm-≡ dense-closed-two-sided-intervals-with-∞ ·ᵢ-comm)
  ; plus?    = λ i → just (plusᵢ i)
  }

------------------------------------------------------------------------
-- The discrete windows embed

two-sided→dense-closed : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.two-sided-intervals-with-∞
                                     dense-closed-two-sided-intervals-with-∞
two-sided→dense-closed = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-𝟏        = eqᵢ refl refl
  ; map-·        = λ {i} {j} → eqᵢ (#-+ (Discrete.min i) (Discrete.min j))
                                   (ℕ∞→ℚ∞-+ (Discrete.max i) (Discrete.max j))
  ; map-⊤        = eqᵢ refl refl
  ; map-⊔        = λ {i} {j} → eqᵢ (#-⊓ (Discrete.min i) (Discrete.min j))
                                   (ℕ∞→ℚ∞-⊔ (Discrete.max i) (Discrete.max j))
  ; map-ι        = eqᵢ refl refl
  }
  where
    embed : Discrete.Interval∞ → Interval∞
    embed i =
      [ # Discrete.min i
      , ℕ∞→ℚ∞ (Discrete.max i)
      ] {fromWitness (ℕ∞→ℚ∞-mono {Discrete.↑ Discrete.min i} {Discrete.max i}
                                  (Discrete.min≤max i))}

    mono : ∀ {i j} → i Discrete.≾ᵢ j → embed i ≾ᵢ embed j
    mono {i} {j} (minrel , maxrel) =
      #-mono-≤ minrel , ℕ∞→ℚ∞-mono {Discrete.max i} {Discrete.max j} maxrel
