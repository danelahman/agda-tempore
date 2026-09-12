------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the sets of timed traces of                       --
-- `Traces.Timed.RightSided`, read as upper bounds: every run of a  --
-- computation stays within one of the listed bounds. Resource grades   --
-- are the right-sided time intervals, "at most `n` time steps".        --
--                                                                     --
-- The projection measures a grade by its slowest bound:                --
--                                                                     --
--   ∣ P ∣ᵉ  =  [0, the greatest duration among the traces of P ]      --
--                                                                     --
-- which is sound because staying within a bound takes no longer than   --
-- the bound does (`duration-≼ᵃ`), and is the best such bound because   --
-- each listed trace is a run the grade permits. What the resource      --
-- grade forgets is *which* runs there were and which operations they   --
-- performed -- so `⌈ write ⌉` and `⟨ 3 ⟩` become the same deadline,     --
-- though only the first permits a store.                              --
--                                                                     --
-- Monotonicity is where the two orders meet: weakening a grade         --
-- replaces each bound by one that permits at least as much, and a      --
-- bound that permits more takes at least as long.                     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; ⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.RightSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_
open import Syntax.Grades.Traces.Allowance Op costʰⁱ using (duration-≼ᵃ)

open import Syntax.Grades.Example.Traces.Timed.RightSided
  Op _≟ₒ_ costʰⁱ costʰⁱ-pos using (right-sided; _≾_)

open MaxDurations costʰⁱ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest bound

mapₒ : NeTraces → 𝕀ᵣ
mapₒ P = [0, setDuration (traces P) ]

-- monotonicity: each bound of `P` stays within one of `Q`, and so takes
-- no longer than it, hence no longer than `Q`'s slowest

mapₒ-monotone : {P Q : NeTraces} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel =
  bigMax-bound duration (traces P) (setDuration (traces Q)) step
  where
    step : (t : Trace) → t ∈ traces P → duration t ≤ setDuration (traces Q)
    step t t∈P
      with find (toWitness (rel t (fromWitness t∈P)))
    ... | t' , t'∈Q , t≼t' =
          ≤-trans (duration-≼ᵃ t≼t') (bigMax-mem duration t' (traces Q) t'∈Q)

-- the monoid structure is preserved: sequencing two grades adds their
-- worst cases, the language product pairing each bound with each

mapₒ-· : (P Q : NeTraces) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀ᵣ (setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

traces→right-sided-intervals : right-sided →ᵍ right-sided-intervals
traces→right-sided-intervals = record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-of-nat   = λ {n} →
      eq𝕀ᵣ (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))
  }

tracesToRightSidedIntervalsGradeSystem : GradeSystem
tracesToRightSidedIntervalsGradeSystem = record
  { RGrade = right-sided-intervals
  ; EGrade = right-sided
  ; ∣_∣ᵉ   = traces→right-sided-intervals
  }
