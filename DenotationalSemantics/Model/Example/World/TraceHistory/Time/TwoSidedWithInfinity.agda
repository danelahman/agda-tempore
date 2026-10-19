--------------------------------------------------------------------------
-- A trace-history Kripke frame for the two-sided time intervals with a --
-- possibly-infinite right endpoint as the resource grades.             --
--                                                                      --
-- Worlds are timed traces `Trace`, recording the history observed so   --
-- far. A resource grade `[ min , max ]` (with `max : ℕ∞`) reaches the  --
-- histories obtained by appending a continuation `t` whose duration    --
-- falls in the window `[ min , max ]`; an infinite `max` imposes no    --
-- upper bound:                                                         --
--                                                                      --
--   w ⊑ʰ[ i ] w'   iff   w ∙ t ≡ w'   and   min i ≤ dur t   and        --
--                        ↑ dur t ≤∞ max i    (for some continuation t) --
--                                                                      --
-- Multiplying grades (`·ᵢ`) adds the endpoints (with `∞` absorbing),   --
-- matching the addition of durations along the concatenation of        --
-- continuations.                                                       --
--------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)

open import Syntax.Durations.Nat using (ℕᵀ)

module DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinity
  (Op : Set) (c : Op → ℕ) where

open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; ≤-irrelevant; +-mono-≤)
open import Data.Product using (_,_)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_]; min; max; _·ᵢ_; _≾ᵢ_; two-sided-intervals-with-∞;
         ℕ∞; ↑_; ∞; _+∞_; _≤∞_; +∞-mono-≤∞; ≤∞-refl; ≤∞-trans; ≤∞-irrelevant)

open import Syntax.Grades.Traces.Base ℕᵀ Op
open import Syntax.Grades.Traces.Durations ℕᵀ Op
open Durations c

open import Util.Equality

open import DenotationalSemantics.Model.World

-- lifting `≡` into `≤∞`

≤∞-reflexive : ∀ {a b} → a ≡ b → a ≤∞ b
≤∞-reflexive refl = ≤∞-refl

-- Accessibility on trace histories: reach `w'` from `w` by appending a
-- continuation `t` whose duration lies within the window `[ min i , max
-- i ]` (no upper bound when `max i` is infinite).

record _⊑ʰ[_]_ (w : Trace) (i : Interval∞) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont    : Trace                        -- the appended continuation
    extends : w ∙ cont ≡ w'                 -- `w'` is `w` extended by `cont`
    lower   : min i ≤ duration cont         -- its duration is at least `min i`
    upper   : ↑ duration cont ≤∞ max i      -- and at most `max i`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `[ 0 , ↑ 0 ]`: the empty continuation

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ [ 0 , ↑ 0 ] ] w
⊑ʰ-refl {w} = mkʰ ε (∙-identityʳ w) z≤n z≤n

-- transitivity multiplies the grades (adds both endpoints), appending
-- the two continuations

⊑ʰ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ʰ[ ρ₁ ] w' → w' ⊑ʰ[ ρ₂ ] w'' → w ⊑ʰ[ ρ₁ ·ᵢ ρ₂ ] w''
⊑ʰ-trans {ρ₁} {ρ₂} {w} (mkʰ t₁ eq₁ lo₁ hi₁) (mkʰ t₂ eq₂ lo₂ hi₂) =
  mkʰ (t₁ ∙ t₂)
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
      (≤-trans (+-mono-≤ lo₁ lo₂) (≤-reflexive (sym (duration-∙ t₁ t₂))))
      (≤∞-trans (≤∞-reflexive (cong ↑_ (duration-∙ t₁ t₂)))
                (+∞-mono-≤∞ {↑ duration t₁} {↑ duration t₂} {max ρ₁} {max ρ₂}
                            hi₁ hi₂))

-- covariance: a wider window (a larger interval) gives a larger relation

⊑ʰ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵢ ρ₂ → w ⊑ʰ[ ρ₁ ] w' → w ⊑ʰ[ ρ₂ ] w'
⊑ʰ-mono (minrel , maxrel) (mkʰ cont eq lo hi) =
  mkʰ cont eq (≤-trans minrel lo) (≤∞-trans hi maxrel)

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the remaining witnesses are irrelevant proofs

⊑ʰ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ʰ[ ρ ] w') → p ≡ q
⊑ʰ-irrelevant {ρ} {w} (mkʰ t refl lo hi) (mkʰ t' eq' lo' hi')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl with ≤-irrelevant lo lo'
... | refl with ≤∞-irrelevant hi hi'
... | refl = refl

-- The frame.

histories : World two-sided-intervals-with-∞
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ʰ[_]_
  ; ⊑-refl       = ⊑ʰ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
