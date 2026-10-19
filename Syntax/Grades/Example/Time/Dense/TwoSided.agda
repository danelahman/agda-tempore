------------------------------------------------------------------------
-- Two-sided intervals of dense time, each end open or closed and the --
-- right-hand one possibly absent, as grades.                         --
--                                                                    --
-- A grade bounds the elapsed time from both sides: `[ p , a ]`       --
-- "between `p` and `a` time units" inclusive, `p` a non-negative     --
-- rational and `a` an extended one, `∞` imposing no upper bound; an  --
-- open end is written with the bracket turned outwards, ISO style:   --
-- `] p , a ]` is "more than `p`", `[ p , a [` "less than `a`", and   --
-- `[ p , ∞ [` and `[ p , ∞ ]` are the same grade. A delay by `q` has --
-- grade `[ q , ↑ q ]`.                                               --
--                                                                    --
-- This is `Example.Time.Intervals` at the rational time domain: the  --
-- intervals are the convex sets of durations, ordered by containment --
-- and sequenced by the Minkowski sum (`Durations.Intervals.Dense`).  --
-- The closed intervals of `Time.Dense.TwoSidedClosed` are a          --
-- sub-grade (`closed→strict`), and the discrete windows of           --
-- `Time.TwoSidedWithInfinity` embed along the inclusion of durations --
-- (`two-sided→dense`).                                               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Time.Dense.TwoSided where

open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (True; fromWitness)

open import Syntax.Durations using (_→ᴰ_)
open import Syntax.Durations.NonNegativeRational
  using (ℚ≥0ᴰ; ℚ≥0ᵀ; ℕ→ℚ≥0ᴰ)
open import Syntax.Grades using (Grade; GradeMorphism)

open import Util.Equality

open import Syntax.Grades.Example.Time.Dense.ExtendedRational public
  using (ℚ∞; ↑_; ∞; _/_; #_; nonZero)
open import Syntax.Grades.Example.Time.Dense.ExtendedRational
  using (ℚ≥0; _≤_; _≤?_; _⊓_; _⊔_; _≤∞_; _+∞_; _⊔∞_;
         p≤q⇒p⊓q≡p; p≥q⇒p⊓q≡q; p≤q⇒p⊔q≡q; p≥q⇒p⊔q≡p)

open import Syntax.Durations.Monus ℚ≥0ᵀ using (_⊓ᴰ_; _⊔ᴰ_; <⇒≤)

open import Syntax.Grades.Example.Time.Intervals ℚ≥0ᵀ public
  renaming (∞ to ∞ʰ)

import Syntax.Grades.Example.Time.Dense.TwoSidedClosed as Closed
import Syntax.Grades.Example.Time.TwoSidedWithInfinity as Discrete

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

dense-two-sided-intervals-with-∞ : Grade ℚ≥0ᴰ
dense-two-sided-intervals-with-∞ = intervals

------------------------------------------------------------------------
-- The closed intervals are a sub-grade

private
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

  -- a closed interval is nonempty
  closed◁ : ∀ {p a} → ↑ p ≤∞ a → (p ∣ ⁻) ◁ ⌈ a ⌉
  closed◁ {p} {↑ q} r = ⊑-⊏-trans (≤⇒⁻⊑⁻ r) (⊏-by-side refl)
  closed◁ {p} {∞}   _ = tt

closed : Closed.Interval∞ → Interval
closed i = ⟪ Closed.min i ∣ ⁻ , ⌈ Closed.max i ⌉ ⟫
             {fromWitness (closed◁ {Closed.min i} {Closed.max i} (Closed.min≤max i))}

closed→strict : GradeMorphism Syntax.Durations.idᴰ Closed.dense-closed-two-sided-intervals-with-∞
                                                   dense-two-sided-intervals-with-∞
closed→strict = record
  { map          = closed
  ; map-monotone = λ { {i} {j} (r , r') → ≤⇒⁻⊑⁻ r , ⌈⌉-mono {Closed.max i} {Closed.max j} r' }
  ; map-u        = eqⁱ refl refl
  ; map-·        = λ {i} {j} → eqⁱ refl (⌈⌉-+ (Closed.max i) (Closed.max j))
  ; map-⊤        = eqⁱ refl refl
  ; map-⊔        = λ {i} {j} →
      eqⁱ (trans (cong (_∣ ⁻) (⊓-⊓ᴰ (Closed.min i) (Closed.min j)))
                 (sym (⊓ᶜ-⁻ (Closed.min i) (Closed.min j))))
          (⌈⌉-⊔ (Closed.max i) (Closed.max j))
  ; map-of-dur   = eqⁱ refl refl
  }

------------------------------------------------------------------------
-- The discrete windows embed, through the closed intervals

two-sided→dense : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.two-sided-intervals-with-∞
                                     dense-two-sided-intervals-with-∞
two-sided→dense = record
  { map          = λ i → closed (D.map i)
  ; map-monotone = λ {i} {j} r →
      S.map-monotone {D.map i} {D.map j} (D.map-monotone {i} {j} r)
  ; map-u        = trans (cong closed D.map-u) S.map-u
  ; map-·        = λ {i} {j} →
      trans (cong closed (D.map-· {i} {j})) (S.map-· {D.map i} {D.map j})
  ; map-⊤        = trans (cong closed D.map-⊤) S.map-⊤
  ; map-⊔        = λ {i} {j} →
      trans (cong closed (D.map-⊔ {i} {j})) (S.map-⊔ {D.map i} {D.map j})
  ; map-of-dur   = trans (cong closed D.map-of-dur) S.map-of-dur
  }
  where
    module D = GradeMorphism Closed.two-sided→dense-closed
    module S = GradeMorphism closed→strict
