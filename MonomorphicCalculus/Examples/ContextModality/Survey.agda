------------------------------------------------------------------------
-- Is the unit the greatest grade (`⊤ ≾ 𝟏`)?                          --
--                                                                    --
-- The context modality is a parametric right adjoint at every grade  --
-- exactly when `⊤ ≾ 𝟏` (`PRA-everywhere` in                          --
-- `Renaming/ContextModality/LowerBounds`, and `PRA-⊤⇒⊤≾𝟏` in         --
-- `Renaming/ContextModality`); otherwise `L_⊤` is not one.           --
--                                                                    --
-- How to read it                                                     --
--   Each line below runs the grade's own decision procedure `⊤ ≾? 𝟏` --
--   and checks the answer with `refl`.                               --
------------------------------------------------------------------------

open import Data.Bool.Base using (Bool; true; false)
open import Relation.Nullary.Decidable using (does)

open import Grades.Base
open import Grades.Durations using (Duration)
open import Grades.Durations.Nat using (ℕᴰ)

open import Util.Equality

module MonomorphicCalculus.Examples.ContextModality.Survey where

⊤≾𝟏? : {D : Duration} → Grade D → Bool
⊤≾𝟏? G = does (Grade._≾?_ G (Grade.⊤ G) (Grade.𝟏 G))

------------------------------------------------------------------------
-- Time

open import Grades.Examples.Time.RightSided using (right-sided-intervals)
open import Grades.Examples.Time.LeftSided
  using (left-sided-intervals; left-sided-intervals-with-⊤)
open import Grades.Examples.Time.TwoSidedWithInfinity
  using (two-sided-intervals-with-∞; two-sided-intervals-with-⊤)
open import Grades.Examples.Time.Dense.RightSided using (dense-right-sided-intervals)
open import Grades.Examples.Time.Dense.LeftSided using (dense-left-sided-intervals)
open import Grades.Examples.Time.Dense.RightSidedCut using (dense-right-sided-cut-intervals)
open import Grades.Examples.Time.Dense.LeftSidedCut using (dense-left-sided-cut-intervals)
open import Grades.Examples.Time.Dense.TwoSided using (dense-two-sided-intervals-with-∞)
open import Grades.Examples.Time.Dense.TwoSidedClosed
  using (dense-closed-two-sided-intervals-with-∞)

time-right    : ⊤≾𝟏? right-sided-intervals ≡ false
time-right    = refl
time-left     : ⊤≾𝟏? left-sided-intervals ≡ true
time-left     = refl
time-left-⊤   : ⊤≾𝟏? left-sided-intervals-with-⊤ ≡ false
time-left-⊤   = refl
time-two      : ⊤≾𝟏? two-sided-intervals-with-∞ ≡ false
time-two      = refl
time-two-⊤    : ⊤≾𝟏? two-sided-intervals-with-⊤ ≡ false
time-two-⊤    = refl
dense-right   : ⊤≾𝟏? dense-right-sided-intervals ≡ false
dense-right   = refl
dense-left    : ⊤≾𝟏? dense-left-sided-intervals ≡ true
dense-left    = refl
dense-right-cut : ⊤≾𝟏? dense-right-sided-cut-intervals ≡ false
dense-right-cut = refl
dense-left-cut  : ⊤≾𝟏? dense-left-sided-cut-intervals ≡ true
dense-left-cut  = refl
dense-two     : ⊤≾𝟏? dense-two-sided-intervals-with-∞ ≡ false
dense-two     = refl
dense-two-closed : ⊤≾𝟏? dense-closed-two-sided-intervals-with-∞ ≡ false
dense-two-closed = refl

------------------------------------------------------------------------
-- Counts, levels, products, semidirect products

open import Grades.Examples.Counts.AtLeast using (at-least-counts; at-least-counts-with-⊤)
open import Grades.Examples.Counts.AtMost using (at-most-counts)
open import Grades.Examples.Counts.UpperBound using (counts-upper-bound)
open import Grades.Examples.SecurityLevel using (two-point-levels; taint-sets)
open import Grades.Examples.Product.LeftSidedTimeLevel using (left-sided-time×low-high)
open import Grades.Examples.Product.RightSidedTimeLevel using (right-sided-time×low-high)
open import Grades.Examples.Product.RightSidedTimeEnergy using (energy; right-sided-time×energy)
open import Grades.Examples.SemiDirect.WindowedSchedules using (durations; windowed-schedules)
open import Grades.Examples.SemiDirect.ModeTimes using (mode-times)
open import Grades.Examples.SemiDirect.ResourceLevels using (one-resource; resource-levels)
open import Grades.Examples.SemiDirect.ModeSwitchCosts using (mode-switch-costs)
open import Grades.Examples.Worked.SemiDirect.FlowLevels using (flow)

at-least-2      : ⊤≾𝟏? (at-least-counts 2) ≡ true
at-least-2      = refl
at-least-2-⊤    : ⊤≾𝟏? (at-least-counts-with-⊤ 2) ≡ false
at-least-2-⊤    = refl
at-most-2       : ⊤≾𝟏? (at-most-counts 2) ≡ false
at-most-2       = refl
upper-bound     : ⊤≾𝟏? counts-upper-bound ≡ false
upper-bound     = refl
levels          : ⊤≾𝟏? (two-point-levels {ℕᴰ}) ≡ false
levels          = refl
taint-2         : ⊤≾𝟏? (taint-sets {ℕᴰ} 2) ≡ false
taint-2         = refl
left×level      : ⊤≾𝟏? left-sided-time×low-high ≡ false
left×level      = refl
right×level     : ⊤≾𝟏? right-sided-time×low-high ≡ false
right×level     = refl
energy′         : ⊤≾𝟏? energy ≡ false
energy′         = refl
right×energy    : ⊤≾𝟏? right-sided-time×energy ≡ false
right×energy    = refl
durations′      : ⊤≾𝟏? durations ≡ false
durations′      = refl
windowed        : ⊤≾𝟏? windowed-schedules ≡ false
windowed        = refl
mode-times′     : ⊤≾𝟏? mode-times ≡ false
mode-times′     = refl
one-resource′   : ⊤≾𝟏? (one-resource {ℕᴰ}) ≡ false
one-resource′   = refl
resource-levels′ : ⊤≾𝟏? (resource-levels {ℕᴰ}) ≡ false
resource-levels′ = refl
mode-switch     : ⊤≾𝟏? (mode-switch-costs {ℕᴰ}) ≡ false
mode-switch     = refl
flow′           : ⊤≾𝟏? flow ≡ false
flow′           = refl

------------------------------------------------------------------------
-- Trace grades, at the worked examples' operations

open import Data.Fin.Base using (zero)
open import Data.Nat.Properties using (<⇒≢)
open import Grades.Durations.Nat using (ℕᵀ)

module Timed where
  open import Grades.Examples.Worked.Operations
    using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costˡᵒ; costʰⁱ; cost-≤; costʰⁱ-pos)

  open import Grades.Examples.Traces.Timed.LeftSided
    ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (left-sided)
  open import Grades.Examples.Traces.Timed.RightSided
    ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
    using (right-sided)
  open import Grades.Examples.Traces.Timed.TwoSided
    ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
    using (two-sided)
  open import Grades.Examples.Traces.Subsets.RightSided
    Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans using () renaming (right-sided to subsets)

  timed-floor : ⊤≾𝟏? left-sided ≡ true
  timed-floor = refl
  timed-cap   : ⊤≾𝟏? right-sided ≡ false
  timed-cap   = refl
  timed-two   : ⊤≾𝟏? two-sided ≡ false
  timed-two   = refl
  subsets-cap : ⊤≾𝟏? subsets ≡ false
  subsets-cap = refl

module Regular where
  open import Grades.Examples.Worked.Traces.Regular.Base using (Op; code; code-injective)
  open import Grades.Examples.Traces.Regular.RightSided Op 2 code code-injective
    using (right-sided)
  open import Grades.Regular.Grade 2 zero using (regular-grade)

  regular-cap : ⊤≾𝟏? right-sided ≡ false
  regular-cap = refl
  regular     : ⊤≾𝟏? regular-grade ≡ false
  regular     = refl

module RigidFinite where
  open import Grades.Examples.Worked.Traces.Rigid.Finite.Operations
    using (Op; code; name; name-code; code-name; running)
  open import Grades.Examples.Traces.Rigid.Finite.LeftSided
    Op 3 code name name-code code-name running using (left-sided)
  open import Grades.Examples.Traces.Rigid.Finite.RightSided
    Op 3 code name name-code code-name running using (right-sided)
  open import Grades.Examples.Traces.Rigid.Finite.TwoSided
    Op 3 code name name-code code-name running using (two-sided)
  open import Grades.Examples.Traces.Rigid.Rational.LeftSided
    Op 3 code name name-code code-name running using () renaming (left-sided to ratˡ)
  open import Grades.Examples.Traces.Rigid.Rational.RightSided
    Op 3 code name name-code code-name running using () renaming (right-sided to ratʳ)
  open import Grades.Examples.Traces.Rigid.Rational.TwoSided
    Op 3 code name name-code code-name running using () renaming (two-sided to ratᵗ)

  finite-floor : ⊤≾𝟏? left-sided ≡ false
  finite-floor = refl
  finite-cap   : ⊤≾𝟏? right-sided ≡ false
  finite-cap   = refl
  finite-two   : ⊤≾𝟏? two-sided ≡ false
  finite-two   = refl
  rational-floor : ⊤≾𝟏? ratˡ ≡ false
  rational-floor = refl
  rational-cap   : ⊤≾𝟏? ratʳ ≡ false
  rational-cap   = refl
  rational-two   : ⊤≾𝟏? ratᵗ ≡ false
  rational-two   = refl

module RigidRegular where
  open import Grades.Examples.Worked.Traces.Rigid.Regular.RightSided
    using (Op; code; name; name-code; code-name; running)
  open import Grades.Examples.Traces.Rigid.Regular.LeftSided
    Op 3 code name name-code code-name running using (left-sided)
  open import Grades.Examples.Traces.Rigid.Regular.RightSided
    Op 3 code name name-code code-name running using (right-sided)
  open import Grades.Examples.Traces.Rigid.Regular.TwoSided
    Op 3 code name name-code code-name running using (two-sided)

  regular-floor : ⊤≾𝟏? left-sided ≡ false
  regular-floor = refl
  regular-cap   : ⊤≾𝟏? right-sided ≡ false
  regular-cap   = refl
  regular-two   : ⊤≾𝟏? two-sided ≡ false
  regular-two   = refl
