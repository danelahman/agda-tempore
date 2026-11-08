------------------------------------------------------------------------
-- Is the unit `𝟏` of the grades the greatest grade (`⊤ ≾ 𝟏`)?        --
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

open import Grades.Examples.Time.UpperBound
  using () renaming (upper-bound to time-upper-bound)
open import Grades.Examples.Time.LowerBound
  using () renaming (lower-bound to time-lower-bound; lower-bound-with-⊤ to time-lower-bound-with-⊤)
open import Grades.Examples.Time.Interval
  using () renaming (interval to time-interval; interval-with-⊤ to time-interval-with-⊤)
open import Grades.Examples.Time.Rational.UpperBound using (rational-upper-bound)
open import Grades.Examples.Time.Rational.LowerBound using (rational-lower-bound)
open import Grades.Examples.Time.Rational.UpperBoundCut using (rational-upper-bound-cut)
open import Grades.Examples.Time.Rational.LowerBoundCut using (rational-lower-bound-cut)
open import Grades.Examples.Time.Rational.Interval using (rational-interval)
open import Grades.Examples.Time.Rational.IntervalClosed
  using (rational-closed-interval)

time-upper-bound′         : ⊤≾𝟏? time-upper-bound ≡ false
time-upper-bound′         = refl
time-lower-bound′         : ⊤≾𝟏? time-lower-bound ≡ true
time-lower-bound′         = refl
time-lower-bound-with-⊤′  : ⊤≾𝟏? time-lower-bound-with-⊤ ≡ false
time-lower-bound-with-⊤′  = refl
time-interval′            : ⊤≾𝟏? time-interval ≡ false
time-interval′            = refl
time-interval-with-⊤′     : ⊤≾𝟏? time-interval-with-⊤ ≡ false
time-interval-with-⊤′     = refl
rational-upper-bound′     : ⊤≾𝟏? rational-upper-bound ≡ false
rational-upper-bound′     = refl
rational-lower-bound′     : ⊤≾𝟏? rational-lower-bound ≡ true
rational-lower-bound′     = refl
rational-upper-bound-cut′ : ⊤≾𝟏? rational-upper-bound-cut ≡ false
rational-upper-bound-cut′ = refl
rational-lower-bound-cut′ : ⊤≾𝟏? rational-lower-bound-cut ≡ true
rational-lower-bound-cut′ = refl
rational-interval′        : ⊤≾𝟏? rational-interval ≡ false
rational-interval′        = refl
rational-closed-interval′ : ⊤≾𝟏? rational-closed-interval ≡ false
rational-closed-interval′ = refl

------------------------------------------------------------------------
-- Counts, levels, products, semidirect products

open import Grades.Examples.Counts.AtLeast using (at-least-counts; at-least-counts-with-⊤)
open import Grades.Examples.Counts.AtMost using (at-most-counts)
open import Grades.Examples.Counts.AtMost.ByName using (at-most-counts-by-name)
open import Grades.Examples.Lattice using (low-high; taint-sets)
open import Grades.Examples.Product.TimeLowerBoundLattice using (time-lower-bound×low-high)
open import Grades.Examples.Product.TimeUpperBoundLattice using (time-upper-bound×low-high)
open import Grades.Examples.Product.TimeUpperBoundEnergy using (energy; time-upper-bound×energy)
open import Grades.Examples.SemiDirect.CallTimeSets using (durations; call-time-sets)
open import Grades.Examples.SemiDirect.ModeTimes using (mode-times)
open import Grades.Examples.SemiDirect.Watermarks using (one-watermark; watermarks)
open import Grades.Examples.SemiDirect.ModeSwitchCosts using (mode-switch-costs)
open import Grades.Examples.Worked.SemiDirect.FlowSensitiveLevels using (flow)

at-least-2      : ⊤≾𝟏? (at-least-counts 2) ≡ true
at-least-2      = refl
at-least-2-⊤    : ⊤≾𝟏? (at-least-counts-with-⊤ 2) ≡ false
at-least-2-⊤    = refl
at-most-2       : ⊤≾𝟏? (at-most-counts 2) ≡ false
at-most-2       = refl
at-most-by-name : ⊤≾𝟏? at-most-counts-by-name ≡ false
at-most-by-name = refl
low-high′       : ⊤≾𝟏? (low-high {ℕᴰ}) ≡ false
low-high′       = refl
taint-2         : ⊤≾𝟏? (taint-sets {ℕᴰ} 2) ≡ false
taint-2         = refl
time-lower-bound×low-high′ : ⊤≾𝟏? time-lower-bound×low-high ≡ false
time-lower-bound×low-high′ = refl
time-upper-bound×low-high′ : ⊤≾𝟏? time-upper-bound×low-high ≡ false
time-upper-bound×low-high′ = refl
energy′         : ⊤≾𝟏? energy ≡ false
energy′         = refl
time-upper-bound×energy′ : ⊤≾𝟏? time-upper-bound×energy ≡ false
time-upper-bound×energy′ = refl
durations′      : ⊤≾𝟏? durations ≡ false
durations′      = refl
call-time-sets′ : ⊤≾𝟏? call-time-sets ≡ false
call-time-sets′ = refl
mode-times′     : ⊤≾𝟏? mode-times ≡ false
mode-times′     = refl
one-watermark′  : ⊤≾𝟏? (one-watermark {ℕᴰ}) ≡ false
one-watermark′  = refl
watermarks′     : ⊤≾𝟏? (watermarks {ℕᴰ}) ≡ false
watermarks′     = refl
mode-switch     : ⊤≾𝟏? (mode-switch-costs {ℕᴰ}) ≡ false
mode-switch     = refl
flow′           : ⊤≾𝟏? flow ≡ false
flow′           = refl

------------------------------------------------------------------------
-- Trace grades, at the worked examples' operations

open import Data.Fin.Base using (zero)
open import Data.Nat.Properties using (<⇒≢)
open import Grades.Durations.Nat using (ℕᵀ)

module Banked where
  open import Grades.Examples.Worked.Operations
    using (Op; _≟ₒ_; _<ᵒ_; <ᵒ-cmp; <ᵒ-trans; costˡᵒ; costʰⁱ; cost-≤; costʰⁱ-pos)

  open import Grades.Examples.Traces.Banked.LowerBound
    ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ using (lower-bound)
  open import Grades.Examples.Traces.Banked.UpperBound
    ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
    using (upper-bound)
  open import Grades.Examples.Traces.Banked.Interval
    ℕᵀ Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ (λ o e → <⇒≢ (costʰⁱ-pos o) (sym e))
    using (interval)
  open import Grades.Examples.Traces.FiniteRunSets.UpperBound
    Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans using () renaming (upper-bound to finite-run-sets)

  banked-floor         : ⊤≾𝟏? lower-bound ≡ true
  banked-floor         = refl
  banked-cap           : ⊤≾𝟏? upper-bound ≡ false
  banked-cap           = refl
  banked-interval      : ⊤≾𝟏? interval ≡ false
  banked-interval      = refl
  finite-run-sets-cap : ⊤≾𝟏? finite-run-sets ≡ false
  finite-run-sets-cap = refl

module Regular where
  open import Grades.Examples.Worked.Traces.Regular.Base using (Op; code; code-injective)
  open import Grades.Examples.Traces.Regular.UpperBound Op 2 code code-injective
    using (upper-bound)
  open import Grades.Regular.Grade 2 zero using (regular-grade)

  regular-cap : ⊤≾𝟏? upper-bound ≡ false
  regular-cap = refl
  regular     : ⊤≾𝟏? regular-grade ≡ false
  regular     = refl

module TimedRegexFinite where
  open import Grades.Examples.Worked.Traces.TimedRegex.Finite.Operations
    using (Op; code; name; name-code; code-name; running)
  open import Grades.Examples.Traces.TimedRegex.Finite.LowerBound
    Op 3 code name name-code code-name running using (lower-bound)
  open import Grades.Examples.Traces.TimedRegex.Finite.UpperBound
    Op 3 code name name-code code-name running using (upper-bound)
  open import Grades.Examples.Traces.TimedRegex.Finite.Interval
    Op 3 code name name-code code-name running using (interval)
  open import Grades.Examples.Traces.TimedRegex.Rational.LowerBound
    Op 3 code name name-code code-name running using () renaming (lower-bound to ratˡ)
  open import Grades.Examples.Traces.TimedRegex.Rational.UpperBound
    Op 3 code name name-code code-name running using () renaming (upper-bound to ratʳ)
  open import Grades.Examples.Traces.TimedRegex.Rational.Interval
    Op 3 code name name-code code-name running using () renaming (interval to ratᵗ)

  finite-floor : ⊤≾𝟏? lower-bound ≡ false
  finite-floor = refl
  finite-cap   : ⊤≾𝟏? upper-bound ≡ false
  finite-cap   = refl
  finite-interval : ⊤≾𝟏? interval ≡ false
  finite-interval = refl
  rational-regex-floor    : ⊤≾𝟏? ratˡ ≡ false
  rational-regex-floor    = refl
  rational-regex-cap      : ⊤≾𝟏? ratʳ ≡ false
  rational-regex-cap      = refl
  rational-regex-interval : ⊤≾𝟏? ratᵗ ≡ false
  rational-regex-interval = refl

module TimedRegexNat where
  open import Grades.Examples.Worked.Traces.TimedRegex.Nat.UpperBound
    using (Op; code; name; name-code; code-name; running)
  open import Grades.Examples.Traces.TimedRegex.Nat.LowerBound
    Op 3 code name name-code code-name running using (lower-bound)
  open import Grades.Examples.Traces.TimedRegex.Nat.UpperBound
    Op 3 code name name-code code-name running using (upper-bound)
  open import Grades.Examples.Traces.TimedRegex.Nat.Interval
    Op 3 code name name-code code-name running using (interval)

  nat-floor    : ⊤≾𝟏? lower-bound ≡ false
  nat-floor    = refl
  nat-cap      : ⊤≾𝟏? upper-bound ≡ false
  nat-cap      = refl
  nat-interval : ⊤≾𝟏? interval ≡ false
  nat-interval = refl
