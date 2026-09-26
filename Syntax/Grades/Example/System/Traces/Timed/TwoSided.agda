------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.     --
--                                                                    --
-- The effect grades are the two-sided trace intervals of             --
-- `Example.Traces.Timed.TwoSided`: a grade `[ P , Q ]` states that   --
-- whatever the computation did, it covered one of the traces in `P`  --
-- and stayed within one of those in `Q`. The resource grades are the --
-- two-sided time intervals, "between `min` and `max` time steps".    --
--                                                                    --
-- The projection reads each endpoint through durations, in the       --
-- direction in which its set is read and at its own cost model (`P`  --
-- at `costˡᵒ`, `Q` at `costʰⁱ`):                                     --
--                                                                    --
--   ∣ [ P , Q ] ∣ᵉ  =  [ least duration in P , greatest in Q ]       --
--                                                                    --
-- It is the pairing of the two one-sided projections,                --
-- `System.Traces.Timed.LeftSided` and                                --
-- `System.Traces.Timed.RightSided`, and every law is inherited from  --
-- them.                                                              --
--                                                                    --
-- The coherence field of the grade supplies the condition            --
-- `min ≤ max` of the target.                                         --
--                                                                    --
-- The `unbounded` of the cap is measured by `∞`, so the two greatest --
-- grades correspond, `[ u , unbounded ]` above and `[ 0 , ∞ ]`       --
-- below; neither is absorbing.                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ⊔-identityʳ)

open import Data.Unit using (tt)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.TwoSidedWithInfinity

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.List.Base using (_++_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
  using (bigMax-mem; module MaxDurations)

open import Syntax.Grades.Example.Traces.Timed.TwoSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤ costʰⁱ-pos
  using (TwoSided; lo; hi; lo◇hi; _·ᵗˢ_; _⊔ᵗˢ_; ⊤ᵗˢ; of-natᵗˢ; two-sided;
         _≾ᵗˢ_; _◇ˢ₀_)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (Bounds; within_; unbounded; _·ᵇ_; _⊔ᵇ_)
  renaming (_≾_ to _≾ʰⁱ_; Antichain to Antichainʰⁱ; traces to tracesʰⁱ;
            nonempty to nonemptyʰⁱ)

-- the two endpoints are projected exactly as the corresponding
-- one-sided grades are, each at its own cost model

open import Syntax.Grades.Example.Traces.Timed.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using () renaming (Antichain to Antichainˡᵒ; traces to tracesˡᵒ;
                     nonempty to nonemptyˡᵒ)

open import Syntax.Grades.Example.System.Traces.Timed.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (minSetDuration-n) renaming (mapₒ-monotone to mapˡᵒ-monotone)
open import Syntax.Grades.Example.System.Traces.Timed.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (setDuration-n) renaming (mapₒ-monotone₀ to mapʰⁱ-monotone)

open MinDurations costˡᵒ
  using (minSetDuration; minSetDuration-·ˢ; minSetDuration-++)
  renaming (duration to durationˡᵒ; duration-⟨⟩ to duration-⟨⟩ˡᵒ)
open MaxDurations costʰⁱ
  using (setDuration; setDuration-·ˢ; setDuration-++)
  renaming (duration to durationʰⁱ; duration-⟨⟩ to duration-⟨⟩ʰⁱ)

------------------------------------------------------------------------
-- The coherence field gives the target's `min ≤ max`
--
-- Some listed guarantee takes no longer than some listed allowance, and
-- the two aggregations sit on the outside of that pair.

coherent₀ : (P : Antichainˡᵒ) (Q : Antichainʰⁱ) → tracesˡᵒ P ◇ˢ₀ tracesʰⁱ Q
          → minSetDuration (tracesˡᵒ P) ≤ setDuration (tracesʰⁱ Q)
coherent₀ P Q coh
  with find (toWitness coh)
... | p , p∈P , hit
        with find hit
...     | q , q∈Q , p≤q =
          ≤-trans (bigMin-mem durationˡᵒ p (tracesˡᵒ P) p∈P)
                  (≤-trans p≤q (bigMax-mem durationʰⁱ q (tracesʰⁱ Q) q∈Q))

------------------------------------------------------------------------
-- The projection: fastest guarantee below, slowest allowance above, an
-- unbounded allowance being measured by `∞`

capDuration : Bounds → ℕ∞
capDuration (within Q) = ↑ setDuration (tracesʰⁱ Q)
capDuration unbounded  = ∞

coherent : (i : TwoSided)
         → ↑ minSetDuration (tracesˡᵒ (lo i)) ≤∞ capDuration (hi i)
coherent i with hi i | lo◇hi i
... | within Q   | coh = coherent₀ (lo i) Q coh
... | unbounded  | _   = tt

mapₒ : TwoSided → Interval∞
mapₒ i =
  [ minSetDuration (tracesˡᵒ (lo i)) , capDuration (hi i) ] {fromWitness (coherent i)}

-- monotonicity, endpointwise

capDuration-monotone : {P Q : Bounds}
                     → P ≾ʰⁱ Q → capDuration P ≤∞ capDuration Q
capDuration-monotone {within P}  {within Q}  rel =
  mapʰⁱ-monotone {P} {Q} rel
capDuration-monotone {within _}  {unbounded} rel = tt
capDuration-monotone {unbounded} {within _}  ()
capDuration-monotone {unbounded} {unbounded} rel = tt

mapₒ-monotone : {i₁ i₂ : TwoSided} → i₁ ≾ᵗˢ i₂ → mapₒ i₁ ≾ᵢ mapₒ i₂
mapₒ-monotone {i₁} {i₂} (l , h) =
  mapˡᵒ-monotone {lo i₁} {lo i₂} l , capDuration-monotone {hi i₁} {hi i₂} h

-- and the monoid structure, endpointwise: sequencing adds the best
-- cases below and the worst cases above, `∞` absorbing there

capDuration-· : (P Q : Bounds)
              → capDuration (P ·ᵇ Q) ≡ capDuration P +∞ capDuration Q
capDuration-· (within P) (within Q) =
  cong ↑_ (trans (setDuration-n (tracesʰⁱ P ·ˢ tracesʰⁱ Q))
                 (setDuration-·ˢ (tracesʰⁱ P) (tracesʰⁱ Q)
                                 (nonemptyʰⁱ P) (nonemptyʰⁱ Q)))
capDuration-· (within _) unbounded  = refl
capDuration-· unbounded  (within _) = refl
capDuration-· unbounded  unbounded  = refl

mapₒ-· : (i₁ i₂ : TwoSided) → mapₒ (i₁ ·ᵗˢ i₂) ≡ mapₒ i₁ ·ᵢ mapₒ i₂
mapₒ-· i₁ i₂ =
  eqᵢ (trans (minSetDuration-n (tracesˡᵒ (lo i₁) ·ˢ tracesˡᵒ (lo i₂))
                (·ˢ-ne (nonemptyˡᵒ (lo i₁)) (nonemptyˡᵒ (lo i₂))))
             (minSetDuration-·ˢ (tracesˡᵒ (lo i₁)) (tracesˡᵒ (lo i₂))
                (nonemptyˡᵒ (lo i₁)) (nonemptyˡᵒ (lo i₂))))
      (capDuration-· (hi i₁) (hi i₂))

-- joins, endpointwise: the union takes the faster of the two fastest
-- below and the slower of the two slowest above, `∞` absorbing there

capDuration-⊔ : (P Q : Bounds)
              → capDuration (P ⊔ᵇ Q) ≡ capDuration P ⊔∞ capDuration Q
capDuration-⊔ (within P) (within Q) =
  cong ↑_ (trans (setDuration-n (tracesʰⁱ P ++ tracesʰⁱ Q))
                 (setDuration-++ (tracesʰⁱ P) (tracesʰⁱ Q)))
capDuration-⊔ (within _) unbounded  = refl
capDuration-⊔ unbounded  (within _) = refl
capDuration-⊔ unbounded  unbounded  = refl

mapₒ-⊔ : (i₁ i₂ : TwoSided) → mapₒ (i₁ ⊔ᵗˢ i₂) ≡ mapₒ i₁ ⊔ᵢ mapₒ i₂
mapₒ-⊔ i₁ i₂ =
  eqᵢ (trans (minSetDuration-n (tracesˡᵒ (lo i₁) ++ tracesˡᵒ (lo i₂))
                (++-ne (nonemptyˡᵒ (lo i₁)) (nonemptyˡᵒ (lo i₂))))
             (minSetDuration-++ (tracesˡᵒ (lo i₁)) (tracesˡᵒ (lo i₂))
                (nonemptyˡᵒ (lo i₁)) (nonemptyˡᵒ (lo i₂))))
      (capDuration-⊔ (hi i₁) (hi i₂))

two-sided-traces→intervals : two-sided →ᵍ two-sided-intervals-with-∞
two-sided-traces→intervals = record
  { map          = mapₒ
  ; map-monotone = λ {i₁} {i₂} → mapₒ-monotone {i₁} {i₂}
  ; map-u        = eqᵢ refl refl
  ; map-·        = λ {i₁} {i₂} → mapₒ-· i₁ i₂
  ; map-⊤        = eqᵢ refl refl
  ; map-⊔        = λ {i₁} {i₂} → mapₒ-⊔ i₁ i₂
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
