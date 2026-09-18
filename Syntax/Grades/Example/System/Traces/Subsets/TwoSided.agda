------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the two-sided subset intervals                    --
-- `between [ P , Q ]`, and resource grades the two-sided intervals.   --
--                                                                     --
--   ∣ between [ P , Q ] ∣ᵉ  =  [ greatest in P , greatest in Q ]      --
--                                                                     --
-- Both endpoints are measured by their slowest member: below because  --
-- every listed run is demanded, above because any listed run may      --
-- occur. The pair of `System.Traces.Subsets.LeftSided` and            --
-- `System.Traces.Subsets.RightSided`, and every law is theirs.        --
--                                                                     --
-- The target's `min ≤ max` is the grade's coherence field `P ⊆ Q`     --
-- read through durations, so no admissible grade is refused here.     --
--                                                                     --
-- The target is `two-sided-intervals-with-⊤`: `unconstrained` is      --
-- absorbing, `[ 0 , ∞ ]` is not, and no monoid morphism bridges       --
-- the two.                                                            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o) where

open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Relation.Nullary.Decidable using (toWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

open import Syntax.Grades.Example.Traces.Subsets.TwoSided Op _≟ₒ_
  using (TwoSided; lo; hi; lo◇hi; _·ᵇ_; uᵇ; of-natᵇ; _≾ᵇ_;
         Interval; between_; unconstrained; _·ᴵ_; _≾ᴵ_; two-sided)

-- the two endpoints are projected exactly as the corresponding
-- one-sided grades are

open import Syntax.Grades.Example.System.Traces.Subsets.LeftSided Op _≟ₒ_ costˡᵒ
  using () renaming (mapₒ-monotone to mapˡᵒ-monotone)
open import Syntax.Grades.Example.System.Traces.Subsets.RightSided Op _≟ₒ_ costʰⁱ
  using () renaming (mapₒ-monotone₀ to mapʰⁱ-monotone)

open MaxDurations costˡᵒ using ()
  renaming (duration to durationˡᵒ; duration-⟨⟩ to duration-⟨⟩ˡᵒ;
            setDuration to setDurationˡᵒ; setDuration-·ˢ to setDuration-·ˢˡᵒ)
open MaxDurations costʰⁱ using ()
  renaming (duration to durationʰⁱ; duration-⟨⟩ to duration-⟨⟩ʰⁱ;
            setDuration to setDurationʰⁱ; setDuration-·ˢ to setDuration-·ˢʰⁱ;
            setDuration-⊑ to setDuration-⊑ʰⁱ)

------------------------------------------------------------------------
-- The coherence field gives the target's `min ≤ max`
--
-- Raising the cost model first, then enlarging the set.

coherent : (i : TwoSided)
         → setDurationˡᵒ (traces (lo i)) ≤ setDurationʰⁱ (traces (hi i))
coherent i =
  ≤-trans (setDuration-cost costˡᵒ costʰⁱ (traces (lo i)) cost-≤)
          (setDuration-⊑ʰⁱ (traces (lo i)) (traces (hi i)) (toWitness (lo◇hi i)))

------------------------------------------------------------------------
-- The projection: each endpoint by its slowest member

mapₒ : TwoSided → Interval∞
mapₒ i =
  [ setDurationˡᵒ (traces (lo i))
  , ↑ setDurationʰⁱ (traces (hi i))
  , coherent i
  ]

mapₒ-monotone : {i₁ i₂ : TwoSided} → i₁ ≾ᵇ i₂ → mapₒ i₁ ≾ᵢ mapₒ i₂
mapₒ-monotone {i₁} {i₂} (l , h) =
  mapˡᵒ-monotone {lo i₁} {lo i₂} l , mapʰⁱ-monotone {hi i₁} {hi i₂} h

mapₒ-· : (i₁ i₂ : TwoSided) → mapₒ (i₁ ·ᵇ i₂) ≡ mapₒ i₁ ·ᵢ mapₒ i₂
mapₒ-· i₁ i₂ =
  eqᵢ (setDuration-·ˢˡᵒ (traces (lo i₁)) (traces (lo i₂))
                        (nonempty (lo i₁)) (nonempty (lo i₂)))
      (cong ↑_ (setDuration-·ˢʰⁱ (traces (hi i₁)) (traces (hi i₂))
                                 (nonempty (hi i₁)) (nonempty (hi i₂))))

mapₒ-of-nat : {n : ℕ} → mapₒ (of-natᵇ n) ≡ [ n , ↑ n , ≤-refl ]
mapₒ-of-nat {n} =
  eqᵢ (trans (⊔-identityʳ (durationˡᵒ ⟨ n ⟩)) (duration-⟨⟩ˡᵒ n))
      (cong ↑_ (trans (⊔-identityʳ (durationʰⁱ ⟨ n ⟩)) (duration-⟨⟩ʰⁱ n)))

mapᴵ : Interval → Interval∞⊤
mapᴵ (between i)   = window (mapₒ i)
mapᴵ unconstrained = no-window

mapᴵ-monotone : {i₁ i₂ : Interval} → i₁ ≾ᴵ i₂ → mapᴵ i₁ ≾ʷ mapᴵ i₂
mapᴵ-monotone {between i₁}    {between i₂}    rel =
  mapₒ-monotone {i₁} {i₂} rel
mapᴵ-monotone {between _}     {unconstrained} rel = tt
mapᴵ-monotone {unconstrained} {between _}     ()
mapᴵ-monotone {unconstrained} {unconstrained} rel = tt

mapᴵ-· : (i₁ i₂ : Interval) → mapᴵ (i₁ ·ᴵ i₂) ≡ mapᴵ i₁ ·ʷ mapᴵ i₂
mapᴵ-· (between i₁)   (between i₂)   = cong window_ (mapₒ-· i₁ i₂)
mapᴵ-· (between _)    unconstrained  = refl
mapᴵ-· unconstrained  (between _)    = refl
mapᴵ-· unconstrained  unconstrained  = refl

subsets→intervals : two-sided →ᵍ two-sided-intervals-with-⊤
subsets→intervals = record
  { map          = mapᴵ
  ; map-monotone = λ {i₁} {i₂} → mapᴵ-monotone {i₁} {i₂}
  ; map-u        = cong window_ (eqᵢ refl refl)
  ; map-·        = λ {i₁} {i₂} → mapᴵ-· i₁ i₂
  ; map-⊤        = refl
  ; map-of-nat   = λ {n} → cong window_ (mapₒ-of-nat {n})
  }

subsetsToIntervalsGradeSystem : GradeSystem
subsetsToIntervalsGradeSystem = record
  { RGrade = two-sided-intervals-with-⊤
  ; EGrade = two-sided
  ; ∣_∣ᵉ   = subsets→intervals
  }
