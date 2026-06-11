-----------------------------------------------------------------------------
-- Example grade system of two-sided trace intervals as effect grades and  --
-- two-sided time intervals as resource grades -- the *best-case* reading. --
-----------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans)
open import Data.Product using (_,_)

open import Syntax.Grades
open import Syntax.Grades.Time.TwoSidedIntervals
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.GradeSystem.TwoSidedTraceIntervalsToTwoSidedTimeIntervals (S : LanguageSpec) where

open Grade
open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- the construction is parameterised by an assignment of a predetermined
-- interval of execution times to each operation symbol

module _ (time : Op → Interval) where

  -- the two endpoints give the lower and upper per-operation costs

  loCost hiCost : Op → ℕ
  loCost o = min (time o)
  hiCost o = max (time o)

  loCost≤hiCost : (o : Op) → loCost o ≤ hiCost o
  loCost≤hiCost o = min≤max (time o)

  -- the two-sided traces (over all operations) provide the effect
  -- grades; the best-case duration of (sets of) traces provides the
  -- resource time

  open import Syntax.Grades.Traces.TwoSidedTraces Op _≟ₒ_
  open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_
  open import Syntax.Grades.Traces.Base Op

  -- the best-case durations module is parameterised by the cost map, so
  -- we instantiate it once at the lower costs and once at the upper costs

  module Lo = MinDurations loCost
  module Hi = MinDurations hiCost

  -- the endpoint projections of a trace interval are not re-exported by
  -- `TwoSidedTraces`, so we bring them into scope here

  open TraceInterval

  -- a trace interval is sent to the time interval spanned by the
  -- best-case durations of its two sets, with the sets *swapped* across
  -- the endpoints (see the module header for why)

  mapᵢ : TraceInterval → Interval
  mapᵢ I =
    [ Lo.minSetDuration (traces (upper I))
    , Hi.minSetDuration (traces (lower I))
    , ≤-trans
        (Lo.minSetDuration-⊒ (traces (lower I)) (traces (upper I))
           (nonempty (lower I)) (lo⊑up I))
        (minSetDuration-cost loCost hiCost (traces (lower I))
           (nonempty (lower I)) loCost≤hiCost) ]

  -- monotonicity follows from `minSetDuration` being anti-monotone for
  -- the subset order, which lines up with the swapped endpoints

  mapᵢ-monotone : {I J : TraceInterval} → I ≾ᵀ J → mapᵢ I ≾ᵢ mapᵢ J
  mapᵢ-monotone {I} {J} (loRel , hiRel) =
      Lo.minSetDuration-⊒ (traces (upper I)) (traces (upper J)) (nonempty (upper I)) hiRel
    , Hi.minSetDuration-⊒ (traces (lower J)) (traces (lower I)) (nonempty (lower J)) loRel

  -- the monoid structure is preserved because `minSetDuration` is a
  -- homomorphism for the language product of (non-empty) sets of traces

  mapᵢ-· : (I J : TraceInterval) → mapᵢ (I ·ᵀ J) ≡ mapᵢ I ·ᵢ mapᵢ J
  mapᵢ-· [ l₁ , h₁ , b₁ ] [ l₂ , h₂ , b₂ ] =
    eqᵢ (Lo.minSetDuration-·ˢ (traces h₁) (traces h₂) (nonempty h₁) (nonempty h₂))
        (Hi.minSetDuration-·ˢ (traces l₁) (traces l₂) (nonempty l₁) (nonempty l₂))

  -- a pure-delay point interval is sent to the corresponding point in time

  mapᵢ-of-nat : {n : ℕ} → mapᵢ (of-natᵀ n) ≡ [ n , n , ≤-refl ]
  mapᵢ-of-nat {n} =
    eqᵢ (Lo.duration-⟨⟩ n) (Hi.duration-⟨⟩ n)

  tst→tsi-best : two-sided-traces →ᵍ two-sided-intervals
  tst→tsi-best = record
    { map          = mapᵢ
    ; map-monotone = λ {I} {J} → mapᵢ-monotone {I} {J}
    ; map-u        = eqᵢ refl refl
    ; map-·        = λ {I} {J} → mapᵢ-· I J
    ; map-of-nat   = λ {n} → mapᵢ-of-nat {n}
    }
