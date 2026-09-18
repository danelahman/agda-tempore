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
--                                                                     --
-- Each endpoint is measured at its own cost model: `P` at `costˡᵒ`,    --
-- `Q` at `costʰⁱ`.                                                     --
--                                                                     --
-- The cap's unbounded grade `⊤ᵍ` is measured by `∞`, so the two         --
-- greatest grades correspond -- `[ u , ⊤ᵍ ]` above and `[ 0 , ∞ ]`      --
-- below -- and neither is absorbing, both keeping whatever lower bound --
-- follows them.                                                        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ⊔-identityʳ)

open import Data.Unit using (tt)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_
  using (bigMax-mem; module MaxDurations)

open import Syntax.Grades.Example.Traces.Timed.TwoSided
  Op _≟ₒ_ costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos
  using (TwoSided; lo; hi; lo◇hi; _·ᵗˢ_; ⊤ᵗˢ; of-natᵗˢ; two-sided; _≾ᵗˢ_;
         _◇ˢ₀_)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ costʰⁱ costʰⁱ-pos
  using (Bounds; only_; ⊤ᵍ; _·ᵇ_) renaming (_≾_ to _≾ʰⁱ_)

-- the two endpoints are projected exactly as the corresponding
-- one-sided grades are, each at its own cost model

open import Syntax.Grades.Example.System.Traces.Timed.LeftSided
  Op _≟ₒ_ costˡᵒ using () renaming (mapₒ-monotone to mapˡᵒ-monotone)
open import Syntax.Grades.Example.System.Traces.Timed.RightSided
  Op _≟ₒ_ costʰⁱ costʰⁱ-pos
  using () renaming (mapₒ-monotone₀ to mapʰⁱ-monotone)

open MinDurations costˡᵒ using (minSetDuration; minSetDuration-·ˢ)
  renaming (duration to durationˡᵒ; duration-⟨⟩ to duration-⟨⟩ˡᵒ)
open MaxDurations costʰⁱ using (setDuration; setDuration-·ˢ)
  renaming (duration to durationʰⁱ; duration-⟨⟩ to duration-⟨⟩ʰⁱ)

------------------------------------------------------------------------
-- The coherence field gives the target's `min ≤ max`
--
-- Some listed guarantee takes no longer than some listed allowance, and
-- the two aggregations sit on the outside of that pair.

coherent₀ : (P Q : NeTraces) → traces P ◇ˢ₀ traces Q
          → minSetDuration (traces P) ≤ setDuration (traces Q)
coherent₀ P Q coh
  with find (toWitness coh)
... | p , p∈P , hit
        with find hit
...     | q , q∈Q , p≤q =
          ≤-trans (bigMin-mem durationˡᵒ p (traces P) p∈P)
                  (≤-trans p≤q (bigMax-mem durationʰⁱ q (traces Q) q∈Q))

------------------------------------------------------------------------
-- The projection: fastest guarantee below, slowest allowance above, an
-- unbounded allowance being measured by `∞`

capDuration : Bounds → ℕ∞
capDuration (only Q) = ↑ setDuration (traces Q)
capDuration ⊤ᵍ       = ∞

coherent : (i : TwoSided)
         → ↑ minSetDuration (traces (lo i)) ≤∞ capDuration (hi i)
coherent i with hi i | lo◇hi i
... | only Q | coh = coherent₀ (lo i) Q coh
... | ⊤ᵍ     | _   = tt

mapₒ : TwoSided → Interval∞
mapₒ i = [ minSetDuration (traces (lo i)) , capDuration (hi i) , coherent i ]

-- monotonicity, endpointwise

capDuration-monotone : {P Q : Bounds}
                     → P ≾ʰⁱ Q → capDuration P ≤∞ capDuration Q
capDuration-monotone {only P} {only Q} rel = mapʰⁱ-monotone {P} {Q} rel
capDuration-monotone {only _} {⊤ᵍ}     rel = tt
capDuration-monotone {⊤ᵍ}     {only _} ()
capDuration-monotone {⊤ᵍ}     {⊤ᵍ}     rel = tt

mapₒ-monotone : {i₁ i₂ : TwoSided} → i₁ ≾ᵗˢ i₂ → mapₒ i₁ ≾ᵢ mapₒ i₂
mapₒ-monotone {i₁} {i₂} (l , h) =
  mapˡᵒ-monotone {lo i₁} {lo i₂} l , capDuration-monotone {hi i₁} {hi i₂} h

-- and the monoid structure, endpointwise: sequencing adds the best
-- cases below and the worst cases above, `∞` absorbing there

capDuration-· : (P Q : Bounds)
              → capDuration (P ·ᵇ Q) ≡ capDuration P +∞ capDuration Q
capDuration-· (only P) (only Q) =
  cong ↑_ (setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))
capDuration-· (only _) ⊤ᵍ       = refl
capDuration-· ⊤ᵍ       (only _) = refl
capDuration-· ⊤ᵍ       ⊤ᵍ       = refl

mapₒ-· : (i₁ i₂ : TwoSided) → mapₒ (i₁ ·ᵗˢ i₂) ≡ mapₒ i₁ ·ᵢ mapₒ i₂
mapₒ-· i₁ i₂ =
  eqᵢ (minSetDuration-·ˢ (traces (lo i₁)) (traces (lo i₂))
                         (nonempty (lo i₁)) (nonempty (lo i₂)))
      (capDuration-· (hi i₁) (hi i₂))

two-sided-traces→intervals : two-sided →ᵍ two-sided-intervals-with-∞
two-sided-traces→intervals = record
  { map          = mapₒ
  ; map-monotone = λ {i₁} {i₂} → mapₒ-monotone {i₁} {i₂}
  ; map-u        = eqᵢ refl refl
  ; map-·        = λ {i₁} {i₂} → mapₒ-· i₁ i₂
  ; map-of-nat   = λ {n} →
      eqᵢ (duration-⟨⟩ˡᵒ n)
          (cong ↑_ (trans (⊔-identityʳ (durationʰⁱ ⟨ n ⟩)) (duration-⟨⟩ʰⁱ n)))
  }

tracesToTwoSidedIntervalsGradeSystem : GradeSystem
tracesToTwoSidedIntervalsGradeSystem = record
  { RGrade = two-sided-intervals-with-∞
  ; EGrade = two-sided
  ; ∣_∣ᵉ   = two-sided-traces→intervals
  }
