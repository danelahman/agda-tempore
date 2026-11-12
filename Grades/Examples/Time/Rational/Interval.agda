------------------------------------------------------------------------
-- Intervals of rational time, each end open or closed and the upper  --
-- one possibly absent, as grades.                                    --
--                                                                    --
-- A grade bounds the elapsed time from both sides: `[ p , a ]`       --
-- "between `p` and `a` time units" inclusive, `p` a non-negative     --
-- rational and `a` an extended one, `∞` imposing no upper bound; an  --
-- open end is written with the bracket turned outwards, ISO style:   --
-- `] p , a ]` is "more than `p`", `[ p , a [` "less than `a`", and   --
-- `[ p , ∞ [` and `[ p , ∞ ]` are the same grade. A delay by `q` has --
-- grade `[ q , ↑ q ]`.                                               --
--                                                                    --
-- This is `Time.Intervals` at the rational time domain: an interval  --
-- is determined by the durations it admits, and the intervals are    --
-- ordered by containment and sequenced by the Minkowski sum          --
-- (`Durations.Intervals.Dense`).                                     --
-- The closed intervals of `Time.Rational.IntervalClosed` map into    --
-- them by a grade morphism (`closed→interval`), and so do the time   --
-- intervals in whole steps of `Time.Interval`, along the inclusion   --
-- of durations (`interval→rational`).                                --
------------------------------------------------------------------------

module Grades.Examples.Time.Rational.Interval where

open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (True; fromWitness)

open import Grades.Durations using (_→ᴰ_)
open import Grades.Durations.NonNegativeRational
  using (ℚ≥0ᴰ; ℚ≥0ᵀ; ℕ→ℚ≥0ᴰ)
open import Grades.Base using (strictᵍ; Grade; GradeMorphism)
open import Grades.Hints using (GradeHints)

open import Util.Equality

open import Grades.Examples.Time.Rational.ExtendedRational public
  using (ℚ∞; ↑_; ∞; _/_; #_; nonZero)
open import Grades.Examples.Time.Rational.ExtendedRational
  using (ℚ≥0; _≤_; _≤?_; _⊓_; _⊔_; _≤∞_; _+∞_; _⊔∞_;
         p≤q⇒p⊓q≡p; p≥q⇒p⊓q≡q; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p)

open import Grades.Durations.Monus ℚ≥0ᵀ using (_⊓ᴰ_; _⊔ᴰ_; <⇒≤)

open import Grades.Examples.Time.Intervals ℚ≥0ᵀ public
  renaming (∞ to ∞ʰ)

import Grades.Examples.Time.Rational.IntervalClosed as Closed
import Grades.Examples.Time.Interval as Discrete

------------------------------------------------------------------------
-- Literals

-- an extended value as a closed and as an open upper end

⌈_⌉ ⌈_⌉° : ℚ∞ → Hi
⌈ ↑ q ⌉ = fin (q ∣ ⁺)
⌈ ∞ ⌉   = ∞ʰ

⌈ ↑ q ⌉° = fin (q ∣ ⁻)
⌈ ∞ ⌉°   = ∞ʰ

infix 5 [_,_] [_,_[ ]_,_] ]_,_[

[_,_] : (p : ℚ≥0) (a : ℚ∞) → {True ((p ∣ ⁻) ◁? ⌈ a ⌉)} → Interval
[ p , a ] {ne} = ⟪ p ∣ ⁻ , ⌈ a ⌉ ⟫ {ne}

[_,_[ : (p : ℚ≥0) (a : ℚ∞) → {True ((p ∣ ⁻) ◁? ⌈ a ⌉°)} → Interval
[ p , a [ {ne} = ⟪ p ∣ ⁻ , ⌈ a ⌉° ⟫ {ne}

]_,_] : (p : ℚ≥0) (a : ℚ∞) → {True ((p ∣ ⁺) ◁? ⌈ a ⌉)} → Interval
] p , a ] {ne} = ⟪ p ∣ ⁺ , ⌈ a ⌉ ⟫ {ne}

]_,_[ : (p : ℚ≥0) (a : ℚ∞) → {True ((p ∣ ⁺) ◁? ⌈ a ⌉°)} → Interval
] p , a [ {ne} = ⟪ p ∣ ⁺ , ⌈ a ⌉° ⟫ {ne}

-- the grade's operations, under the names of the interval grades

infixl 7 _·ᵢ_ _⊔ᵢ_
infix 4 _≾ᵢ_

_≾ᵢ_ : Interval → Interval → Set
_≾ᵢ_ = _⊆ⁱ_

_·ᵢ_ _⊔ᵢ_ : Interval → Interval → Interval
_·ᵢ_ = _⊕_
_⊔ᵢ_ = _∪ⁱ_

------------------------------------------------------------------------
-- The grade

rational-interval : Grade ℚ≥0ᴰ
rational-interval = domain-interval

rational-intervalʰ : GradeHints rational-interval
rational-intervalʰ = domain-intervalʰ

------------------------------------------------------------------------
-- The closed intervals, by a grade morphism

-- the minimum and maximum of the rationals are those of the time
-- domain

⊓-⊓ᴰ : ∀ p q → p ⊓ q ≡ p ⊓ᴰ q
⊓-⊓ᴰ p q with p ≤? q
... | yes r = p≤q⇒p⊓q≡p r
... | no ¬r = p≥q⇒p⊓q≡q (<⇒≤ ¬r)

⊔-⊔ᴰ : ∀ p q → p ⊔ q ≡ p ⊔ᴰ q
⊔-⊔ᴰ p q with p ≤? q
... | yes r = p≤q⇒p⊔q≡q r
... | no ¬r = p≥q⇒p⊔q≡p (<⇒≤ ¬r)

-- an extended value read as a closed upper end preserves the order,
-- the sum and the larger value

⌈⌉-mono : ∀ {a b} → a ≤∞ b → ⌈ a ⌉ ⊑ʰ ⌈ b ⌉
⌈⌉-mono {↑ _} {↑ _} r = ≤⇒⁺⊑⁺ r
⌈⌉-mono {↑ _} {∞}   _ = tt
⌈⌉-mono {∞}   {∞}   _ = tt

⌈⌉-+ : ∀ a b → ⌈ a +∞ b ⌉ ≡ ⌈ a ⌉ +ʰ ⌈ b ⌉
⌈⌉-+ (↑ _) (↑ _) = refl
⌈⌉-+ (↑ _) ∞     = refl
⌈⌉-+ ∞     _     = refl

⌈⌉-⊔ : ∀ a b → ⌈ a ⊔∞ b ⌉ ≡ ⌈ a ⌉ ⊔ʰ ⌈ b ⌉
⌈⌉-⊔ (↑ p) (↑ q) = cong fin (trans (cong (_∣ ⁺) (⊔-⊔ᴰ p q)) (sym (⊔ᶜ-⁺ p q)))
⌈⌉-⊔ (↑ _) ∞     = refl
⌈⌉-⊔ ∞     _     = refl

private
  -- a closed interval is nonempty
  closed◁ : ∀ {p a} → ↑ p ≤∞ a → (p ∣ ⁻) ◁ ⌈ a ⌉
  closed◁ {p} {↑ q} r = ⊑-⊏-trans (≤⇒⁻⊑⁻ r) (⊏-by-side refl)
  closed◁ {p} {∞}   _ = tt

closed : Closed.Interval∞ → Interval
closed i = ⟪ Closed.min i ∣ ⁻ , ⌈ Closed.max i ⌉ ⟫
             {fromWitness (closed◁ {Closed.min i} {Closed.max i} (Closed.min≤max i))}

closed→interval : GradeMorphism Grades.Durations.idᴰ Closed.rational-closed-interval
                                                   rational-interval
closed→interval = strictᵍ record
  { map          = closed
  ; map-monotone = λ { {i} {j} (r , r') → ≤⇒⁻⊑⁻ r , ⌈⌉-mono {Closed.max i} {Closed.max j} r' }
  ; map-𝟏        = eqⁱ refl refl
  ; map-·        = λ {i} {j} → eqⁱ refl (⌈⌉-+ (Closed.max i) (Closed.max j))
  ; map-⊤        = eqⁱ refl refl
  ; map-⊔        = λ {i} {j} →
      eqⁱ (trans (cong (_∣ ⁻) (⊓-⊓ᴰ (Closed.min i) (Closed.min j)))
                 (sym (⊓ᶜ-⁻ (Closed.min i) (Closed.min j))))
          (⌈⌉-⊔ (Closed.max i) (Closed.max j))
  ; map-ι        = eqⁱ refl refl
  }

------------------------------------------------------------------------
-- The time intervals in whole steps, by a grade morphism through the closed
-- intervals

interval→rational : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.interval
                                     rational-interval
interval→rational = record
  { map          = λ i → closed (D.map i)
  ; map-monotone = λ {i} {j} r →
      S.map-monotone {D.map i} {D.map j} (D.map-monotone {i} {j} r)
  ; map-𝟏        = trG (closed (D.map (Grade.𝟏 Discrete.interval))) (closed (Grade.𝟏 Closed.rational-closed-interval)) (Grade.𝟏 G) (S.map-≃ {c₁ = D.map (Grade.𝟏 Discrete.interval)} {c₁' = Grade.𝟏 Closed.rational-closed-interval} D.map-𝟏) S.map-𝟏
  ; map-·        = λ {i} {j} →
      trG (closed (D.map (Grade._·_ Discrete.interval i j))) (closed (Grade._·_ Closed.rational-closed-interval (D.map i) (D.map j))) (Grade._·_ G (closed (D.map i)) (closed (D.map j))) (S.map-≃ {c₁ = D.map (Grade._·_ Discrete.interval i j)} {c₁' = Grade._·_ Closed.rational-closed-interval (D.map i) (D.map j)} (D.map-· {i} {j})) (S.map-· {D.map i} {D.map j})
  ; map-⊤        = trG (closed (D.map (Grade.⊤ Discrete.interval))) (closed (Grade.⊤ Closed.rational-closed-interval)) (Grade.⊤ G) (S.map-≃ {c₁ = D.map (Grade.⊤ Discrete.interval)} {c₁' = Grade.⊤ Closed.rational-closed-interval} D.map-⊤) S.map-⊤
  ; map-⊔        = λ {i} {j} →
      trG (closed (D.map (Grade._⊔_ Discrete.interval i j))) (closed (Grade._⊔_ Closed.rational-closed-interval (D.map i) (D.map j))) (Grade._⊔_ G (closed (D.map i)) (closed (D.map j))) (S.map-≃ {c₁ = D.map (Grade._⊔_ Discrete.interval i j)} {c₁' = Grade._⊔_ Closed.rational-closed-interval (D.map i) (D.map j)} (D.map-⊔ {i} {j})) (S.map-⊔ {D.map i} {D.map j})
  ; map-ι        = λ {τ} → trG (closed (D.map (Grade.ι Discrete.interval τ))) (closed (Grade.ι Closed.rational-closed-interval (Grades.Durations._→ᴰ_.map ℕ→ℚ≥0ᴰ τ))) (Grade.ι G (Grades.Durations._→ᴰ_.map ℕ→ℚ≥0ᴰ τ)) (S.map-≃ {c₁ = D.map (Grade.ι Discrete.interval τ)} {c₁' = Grade.ι Closed.rational-closed-interval (Grades.Durations._→ᴰ_.map ℕ→ℚ≥0ᴰ τ)} (D.map-ι {τ})) S.map-ι
  }
  where
    module D = GradeMorphism Closed.interval→rational-closed
    module S = GradeMorphism closed→interval
    G = rational-interval
    open Grade using (≃-trans)

    trG : (a b c : Interval) → Grade._≃_ G a b → Grade._≃_ G b c → Grade._≃_ G a c
    trG a b c = ≃-trans G {a} {b} {c}
