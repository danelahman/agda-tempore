------------------------------------------------------------------------
-- Lower bounds on rational time, the end open or closed,             --
-- as grades.                                                         --
--                                                                    --
-- A grade is a lower cut of the non-negative rationals, the interval --
-- `⟨ l , ∞ ⟩` of `Durations.Intervals` with lower end `l`: `≥ p`,    --
-- "at least `p` time units", or `> p`, "more than `p`". The order    --
-- is containment of the durations admitted, so `> p` lies below      --
-- `≥ p` and a larger bound below a smaller one; sequencing adds the  --
-- bounds, the sum strict when a bound summed is; the join is the     --
-- weaker bound; and `≥ 0` is both the unit and the greatest grade. A --
-- delay by `q` has grade `≥ q`.                                      --
--                                                                    --
-- The closed bounds of `Time.Rational.LowerBound` are a sub-grade    --
-- (`closed→cut`), the intervals of `Time.Rational.Interval`          --
-- map onto their lower ends (`interval→cut`), and the discrete       --
-- bounds of `Time.LowerBound` embed along the inclusion of durations --
-- (`lower-bound→rational-cut`).                                      --
------------------------------------------------------------------------

module Grades.Examples.Time.Rational.LowerBoundCut where

open import Data.Maybe.Base using (just; nothing)
open import Data.Product using (_,_; proj₁)

open import Relation.Binary.Definitions using (Decidable; Minimum)
open import Relation.Nullary.Negation.Core using (¬_)

open import Grades.Durations using (idᴰ)
open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ; ℕ→ℚ≥0ᴰ)
open import Grades.Base
open import Grades.Hints using (GradeHints; comm-≡)

open import Util.Equality

open import Util.NonNegativeRational public
  using (ℚ≥0; _/_; #_; nonZero)
open import Util.NonNegativeRational
  using (#-mono-≤; #-+; #-⊓)

open import Grades.Durations.Intervals ℚ≥0ᵀ public

import Grades.Examples.Time.Rational.LowerBound as Closed
import Grades.Examples.Time.Rational.Interval as IntervalGrade
import Grades.Examples.Time.LowerBound as Discrete

------------------------------------------------------------------------
-- The bounds

Lower : Set
Lower = Cut

infix 8 ≥_ >_

≥_ >_ : ℚ≥0 → Lower
≥ p = p ∣ ⁻
> p = p ∣ ⁺

-- the order, the sum and the join

infixl 7 _·ˡ_ _⊔ˡ_
infix 4 _≾ˡ_ _≾ˡ?_

_≾ˡ_ : Lower → Lower → Set
l ≾ˡ l' = l' ⊑ l

_≾ˡ?_ : Decidable _≾ˡ_
l ≾ˡ? l' = l' ⊑? l

_·ˡ_ _⊔ˡ_ : Lower → Lower → Lower
_·ˡ_ = _+ˡ_
_⊔ˡ_ = _⊓ᶜ_

-- sequencing distributes over the join on the right

+ˡ-distribʳ-⊓ᶜ : ∀ c d e → (d +ˡ c) ⊓ᶜ (e +ˡ c) ⊑ (d ⊓ᶜ e) +ˡ c
+ˡ-distribʳ-⊓ᶜ c d e =
  subst₂ _⊑_ (cong₂ _⊓ᶜ_ (+ˡ-comm c d) (+ˡ-comm c e)) (+ˡ-comm c (d ⊓ᶜ e))
         (+ˡ-distrib-⊓ᶜ c d e)

-- the unit is not least: `> 0` lies strictly below it

0⁻-not-least : ¬ Minimum _≾ˡ_ 0⁻
0⁻-not-least least = ⊏-by-side refl (least 0⁺)

------------------------------------------------------------------------
-- The grade

rational-lower-bound-cut : Grade ℚ≥0ᴰ
rational-lower-bound-cut = posetᵍ record
  { Carrier         = Lower
  ; _·_             = _·ˡ_
  ; 𝟏               = 0⁻
  ; _≾_             = _≾ˡ_
  ; ⊤               = 0⁻
  ; _⊔_             = _⊔ˡ_
  ; ι               = ≥_
  ; ·-identityˡ     = +ˡ-identityˡ
  ; ·-identityʳ     = +ˡ-identityʳ
  ; ·-assoc         = +ˡ-assoc
  ; ≾-refl          = ⊑-refl
  ; ≾-trans         = λ r r' → ⊑-trans r' r
  ; ≾-antisym       = λ r r' → ⊑-antisym r' r
  ; ≾-irrelevant    = ⊑-irrelevant
  ; _≾?_            = _≾ˡ?_
  ; ≾-⊤             = 0⁻-least
  ; ⊔-ubˡ           = ⊓ᶜ-lbˡ
  ; ⊔-ubʳ           = ⊓ᶜ-lbʳ
  ; ⊔-lub           = ⊓ᶜ-glb
  ; ·-monoˡ-≾       = λ {c} r → +ˡ-monoˡ c r
  ; ·-monoʳ-≾       = λ {c} r → +ˡ-monoʳ c r
  ; ·-distribˡ-⊔-≾  = +ˡ-distrib-⊓ᶜ
  ; ·-distribʳ-⊔-≾  = +ˡ-distribʳ-⊓ᶜ
  ; ≾-zero-productˡ = λ {c} _ → 0⁻-least c
  ; ≾-zero-productʳ = λ {_} {d} _ → 0⁻-least d
  ; ι-zero          = refl
  ; ι-plus          = refl
  }

-- its hints

rational-lower-bound-cutʰ : GradeHints rational-lower-bound-cut
rational-lower-bound-cutʰ = record
  { 𝟏-least? = nothing
  ; ·-comm?  = just (comm-≡ rational-lower-bound-cut +ˡ-comm)
  ; plus?    = λ c → just (plus-self ⊑-refl (+ˡ-inflate c c))
  }

------------------------------------------------------------------------
-- The closed bounds are a sub-grade

closed→cut : GradeMorphism idᴰ Closed.rational-lower-bound
                               rational-lower-bound-cut
closed→cut = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-𝟏        = refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-ι        = refl
  }
  where
    embed : Closed.𝕀 → Lower
    embed Closed.[ q ,+∞⟩ = ≥ q

    mono : ∀ {i j} → i Closed.≾ₒ j → embed i ≾ˡ embed j
    mono {Closed.[ _ ,+∞⟩} {Closed.[ _ ,+∞⟩} = ≤⇒⁻⊑⁻

    hom : ∀ {i j} → embed (i Closed.·ₒ j) ≡ embed i ·ˡ embed j
    hom {Closed.[ _ ,+∞⟩} {Closed.[ _ ,+∞⟩} = refl

    join : ∀ {i j} → embed (i Closed.⊔ₒ j) ≡ embed i ⊔ˡ embed j
    join {Closed.[ p ,+∞⟩} {Closed.[ q ,+∞⟩} =
      trans (cong (_∣ ⁻) (IntervalGrade.⊓-⊓ᴰ p q)) (sym (⊓ᶜ-⁻ p q))

------------------------------------------------------------------------
-- The intervals map onto their lower ends

interval→cut : GradeMorphism idᴰ IntervalGrade.rational-interval
                                  rational-lower-bound-cut
interval→cut = strictᵍ record
  { map          = lo
  ; map-monotone = proj₁
  ; map-𝟏        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-ι        = refl
  }

------------------------------------------------------------------------
-- The discrete bounds embed

lower-bound→rational-cut : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.lower-bound
                                           rational-lower-bound-cut
lower-bound→rational-cut = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-𝟏        = refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-ι        = refl
  }
  where
    embed : Discrete.𝕀 → Lower
    embed Discrete.[ n ,+∞⟩ = ≥ # n

    mono : ∀ {i j} → i Discrete.≾ₒ j → embed i ≾ˡ embed j
    mono {Discrete.[ _ ,+∞⟩} {Discrete.[ _ ,+∞⟩} r = ≤⇒⁻⊑⁻ (#-mono-≤ r)

    hom : ∀ {i j} → embed (i Discrete.·ₒ j) ≡ embed i ·ˡ embed j
    hom {Discrete.[ m ,+∞⟩} {Discrete.[ n ,+∞⟩} = cong (_∣ ⁻) (#-+ m n)

    join : ∀ {i j} → embed (i Discrete.⊔ₒ j) ≡ embed i ⊔ˡ embed j
    join {Discrete.[ m ,+∞⟩} {Discrete.[ n ,+∞⟩} =
      trans (cong (_∣ ⁻) (trans (#-⊓ m n) (IntervalGrade.⊓-⊓ᴰ (# m) (# n))))
            (sym (⊓ᶜ-⁻ (# m) (# n)))
