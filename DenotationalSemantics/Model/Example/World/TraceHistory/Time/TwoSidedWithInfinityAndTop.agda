------------------------------------------------------------------------
-- A trace-history Kripke frame for the two-sided time intervals with --
-- a possibly infinite right endpoint and a formal greatest grade.    --
--                                                                    --
-- Worlds are timed traces `Trace`, recording the history observed so --
-- far. A grade `window [ min , max ]` reaches the histories obtained --
-- by appending a continuation whose duration lies in the window, as  --
-- in the plain frame; `no-window` bounds neither end and reaches     --
-- every history extending the current one:                           --
--                                                                    --
--   w ⊑ʰ[ window i ] w'  iff  w ∙ t ≡ w'  and  min i ≤ dur t  and    --
--                             ↑ dur t ≤∞ max i   (for some `t`)      --
--   w ⊑ʰ[ no-window ] w'  iff  w ∙ t ≡ w'        (for some `t`)      --
--                                                                    --
-- The relation at `no-window` contains every other, as covariance    --
-- requires of the greatest grade, and is the greatest forward        --
-- relation, appending any continuation; it is closed under           --
-- composition, `no-window` being absorbing.                          --
------------------------------------------------------------------------

open import Data.Nat using (ℕ; _+_; _≤_; z≤n)

open import Syntax.Durations.Nat using (ℕᵀ)

module DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinityAndTop
  (Op : Set) (c : Op → ℕ) where

open import Data.Nat.Properties
  using (≤-trans; ≤-reflexive; ≤-irrelevant; +-mono-≤)
open import Data.Product using (_,_)

open import Syntax.Grades.Example.Time.TwoSidedWithInfinity
  using (Interval∞; [_,_]; min; max;
         Interval∞⊤; window_; no-window; _·ʷ_; _≾ʷ_;
         two-sided-intervals-with-⊤;
         ℕ∞; ↑_; ∞; _+∞_; _≤∞_; +∞-mono-≤∞; ≤∞-refl; ≤∞-trans; ≤∞-irrelevant)

open import Syntax.Grades.Traces.Base ℕᵀ Op
open import Syntax.Grades.Traces.Durations ℕᵀ Op
open Durations c

open import Util.Equality

open import DenotationalSemantics.Model.World

-- lifting `≡` into `≤∞`

≤∞-reflexive : ∀ {a b} → a ≡ b → a ≤∞ b
≤∞-reflexive refl = ≤∞-refl

-- Appending a continuation `t` whose duration lies within the window
-- `[ min i , max i ]` (no upper bound when `max i` is infinite).

record _⊑ʷ[_]_ (w : Trace) (i : Interval∞) (w' : Trace) : Set where
  constructor mkʷ
  field
    cont    : Trace                        -- the appended continuation
    extends : w ∙ cont ≡ w'                 -- `w'` is `w` extended by `cont`
    lower   : min i ≤ duration cont         -- its duration is at least `min i`
    upper   : ↑ duration cont ≤∞ max i      -- and at most `max i`

open _⊑ʷ[_]_

-- Appending any continuation at all.

record _≼ʰ_ (w w' : Trace) : Set where
  constructor mkᵉ
  field
    cont    : Trace                        -- the appended continuation
    extends : w ∙ cont ≡ w'                 -- `w'` is `w` extended by `cont`

≼ʰ-trans : ∀ {w w' w''} → w ≼ʰ w' → w' ≼ʰ w'' → w ≼ʰ w''
≼ʰ-trans {w} (mkᵉ t₁ eq₁) (mkᵉ t₂ eq₂) =
  mkᵉ (t₁ ∙ t₂) (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))

≼ʰ-irrelevant : ∀ {w w'} → (p q : w ≼ʰ w') → p ≡ q
≼ʰ-irrelevant {w} (mkᵉ t refl) (mkᵉ t' eq') with ∙-cancelˡ w eq'
... | refl with eq'
... | refl = refl

-- Accessibility on trace histories, the greatest grade reaching every
-- history extending the current one.

_⊑ʰ[_]_ : Trace → Interval∞⊤ → Trace → Set
w ⊑ʰ[ window i ]  w' = w ⊑ʷ[ i ] w'
w ⊑ʰ[ no-window ] w' = w ≼ʰ w'

-- every grade extends the history

⊑ʰ-forward : ∀ ρ {w w'} → w ⊑ʰ[ ρ ] w' → w ≼ʰ w'
⊑ʰ-forward (window _) (mkʷ t eq _ _) = mkᵉ t eq
⊑ʰ-forward no-window  p              = p

-- reflexivity at the unit grade `window [ 0 , ↑ 0 ]`: the empty
-- continuation

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ window [ 0 , ↑ 0 ] ] w
⊑ʰ-refl {w} = mkʷ ε (∙-identityʳ w) z≤n z≤n

-- transitivity multiplies the grades (adds both endpoints), appending
-- the two continuations; a product with `no-window` is `no-window`

⊑ʰ-trans : ∀ {ρ₁ ρ₂ w w' w''}
         → w ⊑ʰ[ ρ₁ ] w' → w' ⊑ʰ[ ρ₂ ] w'' → w ⊑ʰ[ ρ₁ ·ʷ ρ₂ ] w''
⊑ʰ-trans {window ρ₁} {window ρ₂} {w} (mkʷ t₁ eq₁ lo₁ hi₁) (mkʷ t₂ eq₂ lo₂ hi₂) =
  mkʷ (t₁ ∙ t₂)
      (trans (sym (∙-assoc w t₁ t₂)) (trans (cong (_∙ t₂) eq₁) eq₂))
      (≤-trans (+-mono-≤ lo₁ lo₂) (≤-reflexive (sym (duration-∙ t₁ t₂))))
      (≤∞-trans (≤∞-reflexive (cong ↑_ (duration-∙ t₁ t₂)))
                (+∞-mono-≤∞ {↑ duration t₁} {↑ duration t₂} {max ρ₁} {max ρ₂}
                            hi₁ hi₂))
⊑ʰ-trans {window i}  {no-window} p q = ≼ʰ-trans (⊑ʰ-forward (window i) p) q
⊑ʰ-trans {no-window} {ρ₂}        p q = ≼ʰ-trans p (⊑ʰ-forward ρ₂ q)

-- covariance: a wider window (a larger interval) gives a larger
-- relation, and `no-window` is above every grade

⊑ʰ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ʷ ρ₂ → w ⊑ʰ[ ρ₁ ] w' → w ⊑ʰ[ ρ₂ ] w'
⊑ʰ-mono {window _}  {window _}  (minrel , maxrel) (mkʷ cont eq lo hi) =
  mkʷ cont eq (≤-trans minrel lo) (≤∞-trans hi maxrel)
⊑ʰ-mono {window i}  {no-window} rel p = ⊑ʰ-forward (window i) p
⊑ʰ-mono {no-window} {window _}  ()
⊑ʰ-mono {no-window} {no-window} rel p = p

-- proof irrelevance of the witnesses: the continuation is determined by
-- left cancellation, and the remaining witnesses are irrelevant proofs

⊑ʰ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ʰ[ ρ ] w') → p ≡ q
⊑ʰ-irrelevant {window _} {w} (mkʷ t refl lo hi) (mkʷ t' eq' lo' hi')
  with ∙-cancelˡ w eq'
... | refl with eq'
... | refl with ≤-irrelevant lo lo'
... | refl with ≤∞-irrelevant hi hi'
... | refl = refl
⊑ʰ-irrelevant {no-window} p q = ≼ʰ-irrelevant p q

-- The frame.

histories : World two-sided-intervals-with-⊤
histories = record
  { W             = Trace
  ; _⊑[_]_       = _⊑ʰ[_]_
  ; ⊑-refl       = ⊑ʰ-refl
  ; ⊑-trans      = λ {ρ₁} {ρ₂} → ⊑ʰ-trans {ρ₁} {ρ₂}
  ; ⊑-mono       = λ {ρ₁} {ρ₂} → ⊑ʰ-mono {ρ₁} {ρ₂}
  ; ⊑-irrelevant = λ {ρ} → ⊑ʰ-irrelevant {ρ}
  }
