------------------------------------------------------------------------
-- (Left) one-sided intervals of dense time, the end open or closed,  --
-- as grades.                                                         --
--                                                                    --
-- A grade is a lower cut of the non-negative rationals: `≥ p`, "at   --
-- least `p` time units", or `> p`, "more than `p`" -- the interval   --
-- `⟨ l , ∞ ⟩` of `Durations.Intervals` with lower end `l`. The order --
-- is containment of the durations admitted, so `> p` lies below      --
-- `≥ p` and a larger bound below a smaller one; sequencing adds the  --
-- bounds, the sum strict when a bound summed is; the join is the     --
-- weaker bound; and `≥ 0` is both the unit and the greatest grade. A --
-- delay by `q` has grade `≥ q`.                                      --
--                                                                    --
-- The closed bounds of `Time.Dense.LeftSided` are a sub-grade        --
-- (`closed→cut`), the two-sided intervals of `Time.Dense.TwoSided`   --
-- map onto their lower ends (`two-sided→cut`), and the discrete      --
-- bounds of `Time.LeftSided` embed along the inclusion of durations  --
-- (`left-sided→dense-cut`).                                          --
------------------------------------------------------------------------

module Grades.Examples.Time.Dense.LeftSidedCut where

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

import Grades.Examples.Time.Dense.LeftSided as Closed
import Grades.Examples.Time.Dense.TwoSided as TwoSided
import Grades.Examples.Time.LeftSided as Discrete

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

dense-left-sided-cut-intervals : Grade ℚ≥0ᴰ
dense-left-sided-cut-intervals = posetᵍ record
  { Carrier         = Lower
  ; _·_             = _·ˡ_
  ; u               = 0⁻
  ; _≾_             = _≾ˡ_
  ; ⊤               = 0⁻
  ; _⊔_             = _⊔ˡ_
  ; of-dur          = ≥_
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
  ; of-dur-zero     = refl
  ; of-dur-plus     = refl
  }

-- its hints

dense-left-sided-cut-intervalsʰ : GradeHints dense-left-sided-cut-intervals
dense-left-sided-cut-intervalsʰ = record
  { u-least? = nothing
  ; ·-comm?  = just (comm-≡ dense-left-sided-cut-intervals +ˡ-comm)
  ; plus?    = λ c → just (plus-self ⊑-refl (+ˡ-inflate c c))
  }

------------------------------------------------------------------------
-- The closed bounds are a sub-grade

closed→cut : GradeMorphism idᴰ Closed.dense-left-sided-intervals
                               dense-left-sided-cut-intervals
closed→cut = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-u        = refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-of-dur   = refl
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
      trans (cong (_∣ ⁻) (TwoSided.⊓-⊓ᴰ p q)) (sym (⊓ᶜ-⁻ p q))

------------------------------------------------------------------------
-- The two-sided intervals map onto their lower ends

two-sided→cut : GradeMorphism idᴰ TwoSided.dense-two-sided-intervals-with-∞
                                  dense-left-sided-cut-intervals
two-sided→cut = strictᵍ record
  { map          = lo
  ; map-monotone = proj₁
  ; map-u        = refl
  ; map-·        = refl
  ; map-⊤        = refl
  ; map-⊔        = refl
  ; map-of-dur   = refl
  }

------------------------------------------------------------------------
-- The discrete bounds embed

left-sided→dense-cut : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.left-sided-intervals
                                           dense-left-sided-cut-intervals
left-sided→dense-cut = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-u        = refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-of-dur   = refl
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
      trans (cong (_∣ ⁻) (trans (#-⊓ m n) (TwoSided.⊓-⊓ᴰ (# m) (# n))))
            (sym (⊓ᶜ-⁻ (# m) (# n)))
