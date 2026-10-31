------------------------------------------------------------------------
-- (Right) one-sided intervals of dense time, the end open or closed  --
-- or absent, as grades.                                              --
--                                                                    --
-- A grade is an upper end of `Durations.Intervals` admitting zero,   --
-- the interval `⟨ 0⁻ , h ⟩` with upper end `h`: `≤ ↑ a`, "at most    --
-- `a` time units", `< a`, "less than `a`" for a positive `a`, or     --
-- `≤ ∞`, no bound. The order is containment of the durations         --
-- admitted, so `< a` lies below `≤ ↑ a` and a smaller bound below a  --
-- larger one; sequencing adds the bounds, the sum strict when a      --
-- bound summed is and absent when one is; the join is the weaker     --
-- bound; `≤ ↑ 0` is the unit and the least grade, and `≤ ∞` the      --
-- greatest. A delay by `q` has grade `≤ ↑ q`.                        --
--                                                                    --
-- The closed bounds of `Time.Dense.RightSided` are a sub-grade       --
-- (`closed→cut`), the two-sided intervals of `Time.Dense.TwoSided`   --
-- map onto their upper ends (`two-sided→cut`), and the discrete      --
-- bounds of `Time.RightSided` embed along the inclusion of durations --
-- (`right-sided→dense-cut`).                                         --
------------------------------------------------------------------------

module Grades.Examples.Time.Dense.RightSidedCut where

open import Data.Bool.Properties using (T-irrelevant)
open import Data.Maybe.Base using (just)
open import Data.Product using (_,_; proj₂)
open import Data.Unit using (tt)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary.Decidable.Core using (True; toWitness; fromWitness)

open import Grades.Durations using (idᴰ)
open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ; ℕ→ℚ≥0ᴰ)
open import Grades.Base
open import Grades.Hints using (GradeHints; comm-≡)

open import Util.Equality

open import Grades.Examples.Time.Dense.ExtendedRational public
  using (ℚ≥0; ℚ∞; ↑_; ∞; _/_; #_; nonZero)
open import Grades.Examples.Time.Dense.ExtendedRational
  using (ℕ∞→ℚ∞; ℕ∞→ℚ∞-mono; ℕ∞→ℚ∞-+; ℕ∞→ℚ∞-⊔)

open import Grades.Durations.Monus ℚ≥0ᵀ using (0ᴰ-least)

open import Grades.Durations.Intervals ℚ≥0ᵀ public
  renaming (∞ to ∞ʰ)

import Grades.Examples.Time.Dense.RightSided as Closed
import Grades.Examples.Time.Dense.TwoSided as TwoSided
import Grades.Examples.Time.RightSided as Discrete

open TwoSided using (⌈_⌉; ⌈⌉-mono; ⌈⌉-+; ⌈⌉-⊔)

------------------------------------------------------------------------
-- The bounds: an upper end admitting zero

record Upper : Set where
  constructor upper
  field
    bound      : Hi
    {admits0?} : True (fin 0⁺ ⊑ʰ? bound)

open Upper public

admits0 : (x : Upper) → fin 0⁺ ⊑ʰ bound x
admits0 x = toWitness {a? = fin 0⁺ ⊑ʰ? bound x} (admits0? x)

upper! : (h : Hi) → fin 0⁺ ⊑ʰ h → Upper
upper! h r = upper h {fromWitness r}

-- two grades with the same bound are equal

eqᵘ : ∀ {x y} → bound x ≡ bound y → x ≡ y
eqᵘ {_} {y} refl = cong (λ r → upper (bound y) {r}) (T-irrelevant _ _)

-- literals

infix 8 ≤_ <_

≤_ : ℚ∞ → Upper
≤ a = upper! ⌈ a ⌉ (zero≤ a)
  where
    zero≤ : ∀ a → fin 0⁺ ⊑ʰ ⌈ a ⌉
    zero≤ (↑ q) = ≤⇒⁺⊑⁺ (0ᴰ-least q)
    zero≤ ∞     = tt

<_ : (a : ℚ≥0) → {True (fin 0⁺ ⊑ʰ? fin (a ∣ ⁻))} → Upper
<_ a {r} = upper (fin (a ∣ ⁻)) {r}

-- the order, the sum, the unit, the top and the join

infixl 7 _·ᵘ_ _⊔ᵘ_
infix 4 _≾ᵘ_ _≾ᵘ?_

_≾ᵘ_ : Upper → Upper → Set
x ≾ᵘ y = bound x ⊑ʰ bound y

_≾ᵘ?_ : Decidable _≾ᵘ_
x ≾ᵘ? y = bound x ⊑ʰ? bound y

_·ᵘ_ : Upper → Upper → Upper
x ·ᵘ y = upper! (bound x +ʰ bound y)
                (⊑ʰ-trans (admits0 x) (+ʰ-inflate (bound x) (admits0 y)))

uᵘ ⊤ᵘ : Upper
uᵘ = upper! (fin 0⁺) ⊑ʰ-refl
⊤ᵘ = upper ∞ʰ

_⊔ᵘ_ : Upper → Upper → Upper
x ⊔ᵘ y = upper! (bound x ⊔ʰ bound y)
                (⊑ʰ-trans (admits0 x) (⊔ʰ-ubˡ (bound x) (bound y)))

-- sequencing distributes over the join on the right

+ʰ-distribʳ-⊔ʰ : ∀ h k k' → (k ⊔ʰ k') +ʰ h ⊑ʰ (k +ʰ h) ⊔ʰ (k' +ʰ h)
+ʰ-distribʳ-⊔ʰ h k k' =
  subst₂ _⊑ʰ_ (+ʰ-comm h (k ⊔ʰ k')) (cong₂ _⊔ʰ_ (+ʰ-comm h k) (+ʰ-comm h k'))
         (+ʰ-distrib-⊔ʰ h k k')

-- the closure: an upper end that only the point zero or no bound
-- absorbs

plusᵘ : (x : Upper) → Plus _·ᵘ_ _≾ᵘ_ x
plusᵘ x = plus
  (upper! (plusʰ (bound x)) (⊑ʰ-trans (admits0 x) (⊑ʰ-plusʰ (bound x))))
  (⊑ʰ-plusʰ (bound x))
  (plusʰ-iter {bound x} (admits0 x))
  (λ {v} → plusʰ-least {bound x} {bound v})
  (λ {d} → plusʰ-indˡ {bound x} {bound d})
  (λ {d} → plusʰ-indʳ {bound x} {bound d})

------------------------------------------------------------------------
-- The grade

dense-right-sided-cut-intervals : Grade ℚ≥0ᴰ
dense-right-sided-cut-intervals = posetᵍ record
  { Carrier         = Upper
  ; _·_             = _·ᵘ_
  ; u               = uᵘ
  ; _≾_             = _≾ᵘ_
  ; ⊤               = ⊤ᵘ
  ; _⊔_             = _⊔ᵘ_
  ; of-dur          = λ q → ≤ ↑ q
  ; ·-identityˡ     = λ x → eqᵘ (+ʰ-identityˡ (bound x))
  ; ·-identityʳ     = λ x → eqᵘ (+ʰ-identityʳ (bound x))
  ; ·-assoc         = λ x y z → eqᵘ (+ʰ-assoc (bound x) (bound y) (bound z))
  ; ≾-refl          = ⊑ʰ-refl
  ; ≾-trans         = ⊑ʰ-trans
  ; ≾-antisym       = λ r r' → eqᵘ (⊑ʰ-antisym r r')
  ; ≾-irrelevant    = λ {x} {y} → ⊑ʰ-irrelevant {bound x} {bound y}
  ; _≾?_            = _≾ᵘ?_
  ; ≾-⊤             = λ x → ⊑ʰ-∞ (bound x)
  ; ⊔-ubˡ           = λ x y → ⊔ʰ-ubˡ (bound x) (bound y)
  ; ⊔-ubʳ           = λ x y → ⊔ʰ-ubʳ (bound x) (bound y)
  ; ⊔-lub           = λ {x} {y} {z} → ⊔ʰ-lub {bound x} {bound y} {bound z}
  ; ·-monoˡ-≾       = λ {z} r → +ʰ-monoˡ (bound z) r
  ; ·-monoʳ-≾       = λ {z} r → +ʰ-monoʳ (bound z) r
  ; ·-distribˡ-⊔-≾  = λ x y z → +ʰ-distrib-⊔ʰ (bound x) (bound y) (bound z)
  ; ·-distribʳ-⊔-≾  = λ x y z → +ʰ-distribʳ-⊔ʰ (bound x) (bound y) (bound z)
  ; ≾-zero-productˡ = λ {x} {y} r →
      ⊑ʰ-trans (+ʰ-inflate (bound x) (admits0 y)) r
  ; ≾-zero-productʳ = λ {x} {y} r →
      ⊑ʰ-trans (subst (bound y ⊑ʰ_) (+ʰ-comm (bound y) (bound x))
                      (+ʰ-inflate (bound y) (admits0 x))) r
  ; of-dur-zero     = eqᵘ refl
  ; of-dur-plus     = eqᵘ refl
  }

-- its hints

dense-right-sided-cut-intervalsʰ : GradeHints dense-right-sided-cut-intervals
dense-right-sided-cut-intervalsʰ = record
  { u-least? = just admits0
  ; ·-comm?  = just (comm-≡ dense-right-sided-cut-intervals (λ x y → eqᵘ (+ʰ-comm (bound x) (bound y))))
  ; plus?    = λ x → just (plusᵘ x)
  }

------------------------------------------------------------------------
-- The closed bounds are a sub-grade

closed→cut : GradeMorphism idᴰ Closed.dense-right-sided-intervals
                               dense-right-sided-cut-intervals
closed→cut = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-u        = eqᵘ refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = eqᵘ refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-of-dur   = eqᵘ refl
  }
  where
    embed : Closed.𝕀ᵣ → Upper
    embed Closed.[0, a ] = ≤ a

    mono : ∀ {i j} → i Closed.≾ₒ j → embed i ≾ᵘ embed j
    mono {Closed.[0, a ]} {Closed.[0, b ]} = ⌈⌉-mono {a} {b}

    hom : ∀ {i j} → embed (i Closed.·ₒ j) ≡ embed i ·ᵘ embed j
    hom {Closed.[0, a ]} {Closed.[0, b ]} = eqᵘ (⌈⌉-+ a b)

    join : ∀ {i j} → embed (i Closed.⊔ₒ j) ≡ embed i ⊔ᵘ embed j
    join {Closed.[0, a ]} {Closed.[0, b ]} = eqᵘ (⌈⌉-⊔ a b)

------------------------------------------------------------------------
-- The two-sided intervals map onto their upper ends

two-sided→cut : GradeMorphism idᴰ TwoSided.dense-two-sided-intervals-with-∞
                                  dense-right-sided-cut-intervals
two-sided→cut = strictᵍ record
  { map          = embed
  ; map-monotone = proj₂
  ; map-u        = eqᵘ refl
  ; map-·        = eqᵘ refl
  ; map-⊤        = eqᵘ refl
  ; map-⊔        = eqᵘ refl
  ; map-of-dur   = eqᵘ refl
  }
  where
    embed : Interval → Upper
    embed i = upper! (hi i) (◁⇒0⁺⊑ʰ {lo i} {hi i} (lo◁hi i))

------------------------------------------------------------------------
-- The discrete bounds embed

right-sided→dense-cut : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.right-sided-intervals
                                             dense-right-sided-cut-intervals
right-sided→dense-cut = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-u        = eqᵘ refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = eqᵘ refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-of-dur   = eqᵘ refl
  }
  where
    embed : Discrete.𝕀ᵣ → Upper
    embed Discrete.[0, a ] = ≤ ℕ∞→ℚ∞ a

    mono : ∀ {i j} → i Discrete.≾ₒ j → embed i ≾ᵘ embed j
    mono {Discrete.[0, a ]} {Discrete.[0, b ]} r =
      ⌈⌉-mono {ℕ∞→ℚ∞ a} {ℕ∞→ℚ∞ b} (ℕ∞→ℚ∞-mono {a} {b} r)

    hom : ∀ {i j} → embed (i Discrete.·ₒ j) ≡ embed i ·ᵘ embed j
    hom {Discrete.[0, a ]} {Discrete.[0, b ]} =
      eqᵘ (trans (cong ⌈_⌉ (ℕ∞→ℚ∞-+ a b)) (⌈⌉-+ (ℕ∞→ℚ∞ a) (ℕ∞→ℚ∞ b)))

    join : ∀ {i j} → embed (i Discrete.⊔ₒ j) ≡ embed i ⊔ᵘ embed j
    join {Discrete.[0, a ]} {Discrete.[0, b ]} =
      eqᵘ (trans (cong ⌈_⌉ (ℕ∞→ℚ∞-⊔ a b)) (⌈⌉-⊔ (ℕ∞→ℚ∞ a) (ℕ∞→ℚ∞ b)))
