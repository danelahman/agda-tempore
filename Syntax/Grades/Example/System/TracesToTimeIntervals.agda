------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are (non-empty) sets of timed traces, recording which  --
-- runs a computation may have; resource grades are two-sided time      --
-- intervals. The projection reads a set of traces against a per-       --
-- operation interval of execution times, and returns the window        --
-- between its best-case and worst-case duration.                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-trans; ⊔-identityʳ)
open import Data.Product using (_,_)

open import Syntax.Grades
open import Syntax.Grades.Example.Interval.TwoSided
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.Example.System.TracesToTimeIntervals (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

-- the construction is parameterised by an assignment of a predetermined
-- interval of execution times to each operation symbol

module _ (opTime : Op → Interval) where

  -- the two endpoints give the lower and upper per-operation costs

  loCost hiCost : Op → ℕ
  loCost op = min (opTime op)
  hiCost op = max (opTime op)

  loCost≤hiCost : (op : Op) → loCost op ≤ hiCost op
  loCost≤hiCost op = min≤max (opTime op)

  -- the (non-empty) sets of timed traces provide the effect grades, 
  -- the two-sided time intervals provide the resource grades

  open import Syntax.Grades.Example.TraceSet.Inclusion Op _≟ₒ_
  open import Syntax.Grades.Traces.Sets Op
  open import Syntax.Grades.Traces.Durations Op
  open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_
  open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

  -- the best-case durations (aggregated with the lower costs) give the lower
  -- endpoint, the worst-case durations (with the upper costs) the upper endpoint

  module Lo = MinDurations loCost
  module Hi = MaxDurations hiCost

  -- the best-case duration is below the worst-case duration: 
  -- the fastest trace under the lower costs is no slower than itself 
  -- under the upper costs, which in turn is below the slowest trace

  lo-min≤hi-max : (P : NeTraces)
                → Lo.minSetDuration (traces P) ≤ Hi.setDuration (traces P)
  lo-min≤hi-max P with neHead (traces P) (nonempty P)
  ... | t , t∈ =
    ≤-trans (bigMin-mem Lo.duration t (traces P) t∈)
      (≤-trans (duration-mono loCost hiCost loCost≤hiCost t)
               (bigMax-mem Hi.duration t (traces P) t∈))

  -- a set of traces is sent to the interval spanned by its durations

  mapᵢ : NeTraces → Interval
  mapᵢ P =
    [ Lo.minSetDuration (traces P)
    , Hi.setDuration (traces P)
    , lo-min≤hi-max P ]

  -- monotonicity: enlarging the set can only lower the best-case duration
  -- and raise the worst-case one

  mapᵢ-monotone : {P Q : NeTraces} → P ≾ Q → mapᵢ P ≾ᵢ mapᵢ Q
  mapᵢ-monotone {P} {Q} P⊑Q =
      Lo.minSetDuration-⊒ (traces P) (traces Q) (nonempty P) P⊑Q
    , Hi.setDuration-⊑ (traces P) (traces Q) P⊑Q

  -- the monoid structure is preserved because both the best- and the
  -- worst-case set durations are homomorphisms

  mapᵢ-· : (P Q : NeTraces) → mapᵢ (P · Q) ≡ mapᵢ P ·ᵢ mapᵢ Q
  mapᵢ-· P Q =
    eqᵢ (Lo.minSetDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))
        (Hi.setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

  traces→time-intervals : right-sided-traces →ᵍ two-sided-intervals
  traces→time-intervals = record
    { map          = mapᵢ
    ; map-monotone = λ {P} {Q} → mapᵢ-monotone {P} {Q}
    ; map-u        = eqᵢ refl refl
    ; map-·        = λ {P} {Q} → mapᵢ-· P Q
    ; map-of-nat   = λ {n} → eqᵢ (Lo.duration-⟨⟩ n)
                                 (trans (⊔-identityʳ (Hi.duration ⟨ n ⟩)) (Hi.duration-⟨⟩ n))
    }

  traceToIntervalsGradeSystem : GradeSystem
  traceToIntervalsGradeSystem = record
    { RGrade = two-sided-intervals
    ; EGrade = right-sided-traces
    ; ∣_∣ᵉ   = traces→time-intervals
    }
