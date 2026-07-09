------------------------------------------------------------------------
-- A trace-history Kripke frame for the two-sided time intervals as the --
-- resource grades.                                                     --
--                                                                    --
-- Worlds are timed traces `Trace`, recording the history observed so    --
-- far. A two-sided resource grade `[ min , max ]` reaches exactly the    --
-- histories obtained by appending a continuation trace `t` whose         --
-- duration falls in the window `[ min , max ]`:                          --
--                                                                    --
--   w ⊑ʰ[ i ] w'   iff   Σ[ t ] w ∙ t ≡ w'   and   min i ≤ dur t ≤ max i --
--                                                                    --
-- Multiplying grades (`·ᵢ`) adds the two endpoints, matching the        --
-- addition of durations along the concatenation of continuations.       --
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)

module DenotationalSemantics.Model.Example.World.TwoSidedIntervalsWithTraceHistories
  (Op : Set) (c : Op → ℕ) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ≤-irrelevant; +-mono-≤)
open import Data.Product using (_,_)

open import Syntax.Grades.TwoSidedTimeIntervals
  using (Interval; [_,_,_]; min; max; _·ᵢ_; _≾ᵢ_; two-sided-intervals)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open Durations c

open import Util.Equality

open import DenotationalSemantics.Model.World

------------------------------------------------------------------------
-- Left cancellation of trace sequencing
--
-- Prepending a fixed history `w` on the left of a continuation is
-- injective in the continuation.

-- injectivity of `suc⁺`

suc⁺-inj : ∀ {m n} → suc⁺ m ≡ suc⁺ n → m ≡ n
suc⁺-inj refl = refl

-- left cancellation of positive-duration addition

+⁺-cancelˡ : (d : ℕ⁺) {e e' : ℕ⁺} → d +⁺ e ≡ d +⁺ e' → e ≡ e'
+⁺-cancelˡ 𝟏        eq = suc⁺-inj eq
+⁺-cancelˡ (suc⁺ d) eq = +⁺-cancelˡ d (suc⁺-inj eq)

-- a positive duration is never equal to a strictly larger one

d≢d+⁺e : (d e : ℕ⁺) → d +⁺ e ≡ d → ⊥
d≢d+⁺e 𝟏        e ()
d≢d+⁺e (suc⁺ d) e eq = d≢d+⁺e d e (suc⁺-inj eq)

-- injectivity of the `delay` constructor

delay-inj₁ : ∀ {d d' u u'} → delay d u ≡ delay d' u' → d ≡ d'
delay-inj₁ refl = refl

delay-inj₂ : ∀ {d d' u u'} → delay d u ≡ delay d' u' → u ≡ u'
delay-inj₂ refl = refl

-- injectivity of the `operation` constructor (fixed head)

op-inj : ∀ {o u v} → operation o u ≡ operation o v → u ≡ v
op-inj refl = refl

-- injectivity of a delayed operation (fixed delay and head)

delayop-inj : ∀ {d o u v}
            → delay d (operation⁻ o u) ≡ delay d (operation⁻ o v) → u ≡ v
delayop-inj refl = refl

-- prepending a fixed delay is injective in the continuation

prepend-injʳ : (d : ℕ⁺) {t t' : Trace} → prepend d t ≡ prepend d t' → t ≡ t'
prepend-injʳ d {ε}             {ε}             _  = refl
prepend-injʳ d {ε}             {operation _ _} ()
prepend-injʳ d {ε}             {delay e' u'}   eq =
  ⊥-elim (d≢d+⁺e d e' (sym (delay-inj₁ eq)))
prepend-injʳ d {operation _ _} {ε}             ()
prepend-injʳ d {operation _ _} {operation _ _} refl = refl
prepend-injʳ d {operation _ _} {delay e' u'}   eq =
  ⊥-elim (d≢d+⁺e d e' (sym (delay-inj₁ eq)))
prepend-injʳ d {delay e u}     {ε}             eq =
  ⊥-elim (d≢d+⁺e d e (delay-inj₁ eq))
prepend-injʳ d {delay e u}     {operation _ _} eq =
  ⊥-elim (d≢d+⁺e d e (delay-inj₁ eq))
prepend-injʳ d {delay e u}     {delay e' u'}   eq =
  cong₂ delay (+⁺-cancelˡ d (delay-inj₁ eq)) (delay-inj₂ eq)

-- sequencing on the left is injective in the right factor

∙-cancelˡ : (w : Trace) {t t' : Trace} → w ∙ t ≡ w ∙ t' → t ≡ t'
∙-cancelˡ ε                          eq = eq
∙-cancelˡ (operation o s)            eq = ∙-cancelˡ s (op-inj eq)
∙-cancelˡ (delay d ε⁻)               eq = prepend-injʳ d eq
∙-cancelˡ (delay d (operation⁻ o s)) eq = ∙-cancelˡ s (delayop-inj eq)

------------------------------------------------------------------------
-- Accessibility on trace histories
--
-- Reach `w'` from `w` by appending a continuation `t` whose duration
-- lies within the window `[ min i , max i ]`.

infix 5 _⊑ʰ[_]_

record _⊑ʰ[_]_ (w : Trace) (i : Interval) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont    : Trace                        -- the appended continuation
    extends : w ∙ cont ≡ w'                 -- `w'` is `w` extended by `cont`
    lower   : min i ≤ duration cont         -- its duration is at least `min i`
    upper   : duration cont ≤ max i         -- and at most `max i`

open _⊑ʰ[_]_

-- reflexivity at the unit grade `[ 0 , 0 ]`: the empty continuation

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ [ 0 , 0 , z≤n ] ] w
⊑ʰ-refl {w} = mkʰ ε (∙-identityʳ w) z≤n z≤n

-- transitivity multiplies the grades (adds both endpoints), appending
-- the two continuations

⊑ʰ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ʰ[ ρ₁ ] w' → w' ⊑ʰ[ ρ₂ ] w'' → w ⊑ʰ[ ρ₁ ·ᵢ ρ₂ ] w''
⊑ʰ-trans {ρ₁} {ρ₂} {w} (mkʰ t₁ eq₁ lo₁ hi₁) (mkʰ t₂ eq₂ lo₂ hi₂) =
  mkʰ (t₁ ∙ t₂)
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
      (≤-trans (+-mono-≤ lo₁ lo₂) (≤-reflexive (sym (duration-∙ t₁ t₂))))
      (≤-trans (≤-reflexive (duration-∙ t₁ t₂)) (+-mono-≤ hi₁ hi₂))

-- covariance: a wider window (a larger interval) gives a larger relation

⊑ʰ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ᵢ ρ₂ → w ⊑ʰ[ ρ₁ ] w' → w ⊑ʰ[ ρ₂ ] w'
⊑ʰ-mono (minrel , maxrel) (mkʰ t eq lo hi) =
  mkʰ t eq (≤-trans minrel lo) (≤-trans hi maxrel)

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the remaining witnesses are irrelevant proofs

⊑ʰ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ʰ[ ρ ] w') → p ≡ q
⊑ʰ-irrelevant {ρ} {w} (mkʰ t refl lo hi) (mkʰ t' eq' lo' hi')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl with ≤-irrelevant lo lo'
... | refl with ≤-irrelevant hi hi'
... | refl = refl

------------------------------------------------------------------------
-- The frame.

histories : World two-sided-intervals
histories = record
  { W             = Trace
  ; _⊑ʳ[_]_       = _⊑ʰ[_]_
  ; ⊑ʳ-refl       = ⊑ʰ-refl
  ; ⊑ʳ-trans      = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑ʳ-mono       = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑ʳ-irrelevant = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
