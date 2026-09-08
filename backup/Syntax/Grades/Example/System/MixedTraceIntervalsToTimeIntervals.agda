------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- The projection this whole column is named after: a mixed two-sided   --
-- trace interval is sent to the two-sided *time* interval its          --
-- endpoints span --                                                    --
--                                                                     --
--   [ L , U ]  ↦  [ best-case duration of L , worst-case of U ]        --
--                                                                     --
-- which is `Time.TwoSided`'s `[ min , max ]` with the endpoints read   --
-- off traces instead of given outright. The mixed grade is the cell    --
-- that bounds every run from both sides, and this says how: forget     --
-- which runs there were and keep the window they must fall in.         --
--                                                                     --
-- The consistency fields line up too. `min ≤ max` is exactly what the  --
-- grade's own `_◇ˢ_` gives -- some demand fits inside some allowance,  --
-- so the fastest way of meeting the floor is no slower than the        --
-- slowest thing the cap permits -- which the two lifted candidates for --
-- that field would not have supplied on their own.                     --
--                                                                     --
-- Monotonicity is where each endpoint's lift is felt: weakening the    --
-- floor replaces a demand by one below it, which takes no longer, and  --
-- weakening the cap replaces an allowance by one above it, which       --
-- permits no less.                                                     --
--                                                                     --
-- The order lifted is a parameter, as it is for the Kripke frames, so  --
-- both sub-trace orders instantiate this: all that is asked of the     --
-- order is that `duration` be monotone for it.                         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-trans; ⊔-identityʳ)
open import Data.Product using (_,_)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.TwoSided
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

import Syntax.Grades.Traces.Base as Base
import Syntax.Grades.Traces.Durations as Dur
import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.System.MixedTraceIntervalsToTimeIntervals (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

-- The construction is parameterised by an execution time for each
-- operation symbol, by the order the grade lifts, and by monotonicity
-- of the duration for it -- the one property tying the two together.

module _ (cost : Op → ℕ)
         (O : Order.TraceOrder Op)
         (duration-≼ : {s t : Base.Trace Op}
                     → Order.TraceOrder._≼_ O s t
                     → Dur.Durations.duration Op cost s
                     ≤ Dur.Durations.duration Op cost t)
         where

  open import Data.List.Membership.Propositional using (_∈_; find)

  open import Relation.Nullary.Decidable using (toWitness; fromWitness)

  open import Syntax.Grades.Traces.Sets Op
  open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_
  open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

  open import Syntax.Grades.Example.Traces.Lifted.Mixed.TwoSided Op _≟ₒ_ O
    using (MixedInterval; lo; hi; lo◇hi; mixed-two-sided; _≾ᵐⁱ_; _·ᵐⁱ_; uᵐⁱ)

  -- the best-case duration aggregates the floor, the worst-case one the
  -- cap; both charge an operation the same execution time

  module Lo = MinDurations cost
  module Hi = MaxDurations cost

  -- the floor's best case is below the cap's worst case, witnessed by
  -- the pair the grade's consistency field provides

  lo-min≤hi-max : (i : MixedInterval)
                → Lo.minSetDuration (traces (lo i)) ≤ Hi.setDuration (traces (hi i))
  lo-min≤hi-max i
    with find (toWitness (lo◇hi i))
  ... | t , t∈L , hit
          with find hit
  ...     | s , s∈U , t≼s =
            ≤-trans (bigMin-mem Lo.duration t (traces (lo i)) t∈L)
                    (≤-trans (duration-≼ t≼s)
                             (bigMax-mem Hi.duration s (traces (hi i)) s∈U))

  -- an interval of traces is sent to the interval of times it spans

  mapᵢ : MixedInterval → Interval
  mapᵢ i =
    [ Lo.minSetDuration (traces (lo i))
    , Hi.setDuration (traces (hi i))
    , lo-min≤hi-max i ]

  -- monotonicity, one endpoint at a time

  mapᵢ-monotone : {i j : MixedInterval} → i ≾ᵐⁱ j → mapᵢ i ≾ᵢ mapᵢ j
  mapᵢ-monotone {i} {j} (l , h) = lower , upper
    where
      -- a weaker demand is met by a trace no longer than the one that
      -- met the stronger one, so the best case can only drop
      lower : Lo.minSetDuration (traces (lo j)) ≤ Lo.minSetDuration (traces (lo i))
      lower =
        bigMin-bound Lo.duration (traces (lo i))
                     (Lo.minSetDuration (traces (lo j))) (nonempty (lo i)) step
        where
          step : (t : Trace) → t ∈ traces (lo i)
               → Lo.minSetDuration (traces (lo j)) ≤ Lo.duration t
          step t t∈L
            with find (toWitness (l t (fromWitness t∈L)))
          ... | t' , t'∈L' , t'≼t =
                ≤-trans (bigMin-mem Lo.duration t' (traces (lo j)) t'∈L')
                        (duration-≼ t'≼t)

      -- and a larger allowance permits no less, so the worst case can
      -- only rise
      upper : Hi.setDuration (traces (hi i)) ≤ Hi.setDuration (traces (hi j))
      upper =
        bigMax-bound Hi.duration (traces (hi i))
                     (Hi.setDuration (traces (hi j))) step
        where
          step : (s : Trace) → s ∈ traces (hi i)
               → Hi.duration s ≤ Hi.setDuration (traces (hi j))
          step s s∈U
            with find (toWitness (h s (fromWitness s∈U)))
          ... | s' , s'∈U' , s≼s' =
                ≤-trans (duration-≼ s≼s')
                        (bigMax-mem Hi.duration s' (traces (hi j)) s'∈U')

  -- the monoid structure is preserved because both aggregations are
  -- homomorphisms for the language product

  mapᵢ-· : (i j : MixedInterval) → mapᵢ (i ·ᵐⁱ j) ≡ mapᵢ i ·ᵢ mapᵢ j
  mapᵢ-· i j =
    eqᵢ (Lo.minSetDuration-·ˢ (traces (lo i)) (traces (lo j))
                              (nonempty (lo i)) (nonempty (lo j)))
        (Hi.setDuration-·ˢ (traces (hi i)) (traces (hi j))
                           (nonempty (hi i)) (nonempty (hi j)))

  mixed-trace-intervals→time-intervals : mixed-two-sided →ᵍ two-sided-intervals
  mixed-trace-intervals→time-intervals = record
    { map          = mapᵢ
    ; map-monotone = λ {i} {j} → mapᵢ-monotone {i} {j}
    ; map-u        = eqᵢ refl refl
    ; map-·        = λ {i} {j} → mapᵢ-· i j
    ; map-of-nat   = λ {n} → eqᵢ (Lo.duration-⟨⟩ n)
                                 (trans (⊔-identityʳ (Hi.duration ⟨ n ⟩))
                                        (Hi.duration-⟨⟩ n))
    }

  mixedTraceIntervalsToTimeIntervalsGradeSystem : GradeSystem
  mixedTraceIntervalsToTimeIntervalsGradeSystem = record
    { RGrade = two-sided-intervals
    ; EGrade = mixed-two-sided
    ; ∣_∣ᵉ   = mixed-trace-intervals→time-intervals
    }
