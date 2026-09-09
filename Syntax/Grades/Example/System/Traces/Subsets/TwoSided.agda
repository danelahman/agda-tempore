------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the two-sided subset intervals `[ P , Q ]`, and    --
-- resource grades the two-sided time intervals.                        --
--                                                                     --
--   ∣ [ P , Q ] ∣ᵉ  =  [ greatest duration in P , greatest in Q ]     --
--                                                                     --
-- Both endpoints are measured by their slowest member, but for         --
-- opposite reasons: below because every listed run is demanded, above  --
-- because any listed run may occur. So this is the pair of             --
-- `System.Traces.Subsets.LeftSided` and                                --
-- `System.Traces.Subsets.RightSided`, and every law is theirs.         --
--                                                                     --
-- The target's `min ≤ max` is the grade's coherence field `P ⊆ Q`      --
-- read through durations: a larger set has a larger maximum. Since     --
-- that field is exactly the condition for the interval to be           --
-- inhabited, no admissible grade is refused before it reaches here.    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.TwoSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; lo; hi; lo◇hi; _·ᵇ_; two-sided; _≾ᵇ_)

-- the two endpoints are projected exactly as the corresponding
-- one-sided grades are

open import Syntax.Grades.Example.System.Traces.Subsets.LeftSided Op _≟ₒ_ cost
  using () renaming (mapₒ-monotone to mapˡᵒ-monotone)
open import Syntax.Grades.Example.System.Traces.Subsets.RightSided Op _≟ₒ_ cost
  using () renaming (mapₒ-monotone to mapʰⁱ-monotone)

open MaxDurations cost

------------------------------------------------------------------------
-- The coherence field gives the target's `min ≤ max`

coherent : (i : TwoSided)
         → setDuration (traces (lo i)) ≤ setDuration (traces (hi i))
coherent i =
  setDuration-⊑ (traces (lo i)) (traces (hi i)) (toWitness (lo◇hi i))

------------------------------------------------------------------------
-- The projection: each endpoint by its slowest member

mapₒ : TwoSided → Interval
mapₒ i =
  [ setDuration (traces (lo i)) , setDuration (traces (hi i)) , coherent i ]

mapₒ-monotone : {i₁ i₂ : TwoSided} → i₁ ≾ᵇ i₂ → mapₒ i₁ ≾ᵢ mapₒ i₂
mapₒ-monotone {i₁} {i₂} (l , h) =
  mapˡᵒ-monotone {lo i₁} {lo i₂} l , mapʰⁱ-monotone {hi i₁} {hi i₂} h

mapₒ-· : (i₁ i₂ : TwoSided) → mapₒ (i₁ ·ᵇ i₂) ≡ mapₒ i₁ ·ᵢ mapₒ i₂
mapₒ-· i₁ i₂ =
  eqᵢ (setDuration-·ˢ (traces (lo i₁)) (traces (lo i₂))
                      (nonempty (lo i₁)) (nonempty (lo i₂)))
      (setDuration-·ˢ (traces (hi i₁)) (traces (hi i₂))
                      (nonempty (hi i₁)) (nonempty (hi i₂)))

subsets→intervals : two-sided →ᵍ two-sided-intervals
subsets→intervals = record
  { map          = mapₒ
  ; map-monotone = λ {i₁} {i₂} → mapₒ-monotone {i₁} {i₂}
  ; map-u        = eqᵢ refl refl
  ; map-·        = λ {i₁} {i₂} → mapₒ-· i₁ i₂
  ; map-of-nat   = λ {n} →
      eqᵢ (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))
          (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))
  }

subsetsToIntervalsGradeSystem : GradeSystem
subsetsToIntervalsGradeSystem = record
  { RGrade = two-sided-intervals
  ; EGrade = two-sided
  ; ∣_∣ᵉ   = subsets→intervals
  }
