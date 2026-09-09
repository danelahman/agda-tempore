------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the two-sided trace intervals of                   --
-- `Example.Traces.Timed.TwoSided`: a grade `[ P , Q ]` says that       --
-- whatever the computation did, it covered one of the traces in `P`    --
-- and stayed within one of those in `Q`. Resource grades are the       --
-- two-sided time intervals, "between `min` and `max` time steps".      --
--                                                                     --
-- The projection reads each endpoint through durations, and each one   --
-- in the direction its set is read:                                    --
--                                                                     --
--   ∣ [ P , Q ] ∣ᵉ  =  [ least duration in P , greatest duration in Q ] --
--                                                                     --
-- Both sets being read disjunctively, the guarantee is only as strong  --
-- as its cheapest member and the allowance only as tight as its        --
-- slowest. So this is the pair of the two one-sided projections --     --
-- `System.Traces.Timed.LeftSided` and `System.Traces.Timed.RightSided` --
-- -- and every law is theirs.                                          --
--                                                                     --
-- The target's `min ≤ max` is exactly what the grade's coherence field --
-- supplies: some listed guarantee takes no longer than some listed     --
-- allowance, and the least duration of `P` is below that guarantee     --
-- while the greatest of `Q` is above that allowance. Without the field --
-- the projection would not land in the interval grade at all -- which  --
-- is the concrete reason a two-sided trace grade carries one.          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; ⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.TwoSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_
  using (bigMax-mem; module MaxDurations)

open import Syntax.Grades.Example.Traces.Timed.TwoSided Op _≟ₒ_ cost cost-pos
  using (TwoSided; lo; hi; lo◇hi; _·ᵗˢ_; two-sided; _≾ᵗˢ_)

-- the two endpoints are projected exactly as the corresponding
-- one-sided grades are

open import Syntax.Grades.Example.System.Traces.Timed.LeftSided
  Op _≟ₒ_ cost using () renaming (mapₒ-monotone to mapˡᵒ-monotone)
open import Syntax.Grades.Example.System.Traces.Timed.RightSided
  Op _≟ₒ_ cost cost-pos using () renaming (mapₒ-monotone to mapʰⁱ-monotone)

open MinDurations cost
open MaxDurations cost using (setDuration; setDuration-·ˢ)

------------------------------------------------------------------------
-- The coherence field gives the target's `min ≤ max`
--
-- Some listed guarantee takes no longer than some listed allowance, and
-- the two aggregations sit on the outside of that pair.

coherent : (i : TwoSided)
         → minSetDuration (traces (lo i)) ≤ setDuration (traces (hi i))
coherent i
  with find (toWitness (lo◇hi i))
... | p , p∈P , hit
        with find hit
...     | q , q∈Q , p≤q =
          ≤-trans (bigMin-mem duration p (traces (lo i)) p∈P)
                  (≤-trans p≤q (bigMax-mem duration q (traces (hi i)) q∈Q))

------------------------------------------------------------------------
-- The projection: fastest guarantee below, slowest allowance above

mapₒ : TwoSided → Interval
mapₒ i =
  [ minSetDuration (traces (lo i)) , setDuration (traces (hi i)) , coherent i ]

-- monotonicity, endpointwise

mapₒ-monotone : {i₁ i₂ : TwoSided} → i₁ ≾ᵗˢ i₂ → mapₒ i₁ ≾ᵢ mapₒ i₂
mapₒ-monotone {i₁} {i₂} (l , h) =
  mapˡᵒ-monotone {lo i₁} {lo i₂} l , mapʰⁱ-monotone {hi i₁} {hi i₂} h

-- and the monoid structure, endpointwise: sequencing adds the best
-- cases below and the worst cases above

mapₒ-· : (i₁ i₂ : TwoSided) → mapₒ (i₁ ·ᵗˢ i₂) ≡ mapₒ i₁ ·ᵢ mapₒ i₂
mapₒ-· i₁ i₂ =
  eqᵢ (minSetDuration-·ˢ (traces (lo i₁)) (traces (lo i₂))
                         (nonempty (lo i₁)) (nonempty (lo i₂)))
      (setDuration-·ˢ (traces (hi i₁)) (traces (hi i₂))
                      (nonempty (hi i₁)) (nonempty (hi i₂)))

two-sided-traces→intervals : two-sided →ᵍ two-sided-intervals
two-sided-traces→intervals = record
  { map          = mapₒ
  ; map-monotone = λ {i₁} {i₂} → mapₒ-monotone {i₁} {i₂}
  ; map-u        = eqᵢ refl refl
  ; map-·        = λ {i₁} {i₂} → mapₒ-· i₁ i₂
  ; map-of-nat   = λ {n} →
      eqᵢ (duration-⟨⟩ n)
          (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))
  }

tracesToTwoSidedIntervalsGradeSystem : GradeSystem
tracesToTwoSidedIntervalsGradeSystem = record
  { RGrade = two-sided-intervals
  ; EGrade = two-sided
  ; ∣_∣ᵉ   = two-sided-traces→intervals
  }
