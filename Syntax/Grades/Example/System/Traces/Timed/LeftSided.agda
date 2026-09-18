------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the sets of timed traces of                       --
-- `Traces.Timed.LeftSided`, read as guarantees: whatever a          --
-- computation did, it covered one of the listed traces. Resource       --
-- grades are the left-sided time intervals, "at least `n` time steps". --
--                                                                     --
-- The projection measures a grade by its fastest guarantee:            --
--                                                                     --
--   ∣ P ∣ᵉ  =  [ the least duration among the traces of P ,+∞⟩        --
--                                                                     --
-- The *least*, because the set is read disjunctively: which listed     --
-- trace was covered is not known, so all that is guaranteed about the  --
-- time is what the cheapest of them takes. This is sound because       --
-- covering a trace takes at least as long as the trace does            --
-- (`duration-≼ᶜ`), and it is the best such bound because each listed   --
-- trace is a run the grade admits.                                    --
--                                                                     --
-- What the resource grade forgets is *which* operations were performed --
-- -- so `⌈ write ⌉` and `⟨ 3 ⟩` become the same guarantee of elapsed   --
-- time, though only the first guarantees a store happened.            --
--                                                                     --
-- Monotonicity is where the two orders meet: weakening a grade         --
-- replaces each guarantee by an easier one, and an easier guarantee    --
-- takes no longer, so the least duration can only fall.               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (≤-trans)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.LeftSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Timed.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ : Op → ℕ) where

open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MinDuration Op _≟ₒ_
open import Syntax.Grades.Traces.Coverage Op costˡᵒ using (duration-≼ᶜ)

open import Syntax.Grades.Example.Traces.Timed.LeftSided
  Op _≟ₒ_ costˡᵒ using (left-sided; _≾_)

open MinDurations costˡᵒ

------------------------------------------------------------------------
-- The projection: a grade is measured by its fastest guarantee

mapₒ : NeTraces → 𝕀
mapₒ P = [ minSetDuration (traces P) ,+∞⟩

-- monotonicity: each guarantee of `P` is weakened by one of `Q`, which
-- therefore takes no longer, hence at least `Q`'s fastest

mapₒ-monotone : {P Q : NeTraces} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel =
  bigMin-bound duration (traces P) (minSetDuration (traces Q)) (nonempty P) step
  where
    step : (t : Trace) → t ∈ traces P → minSetDuration (traces Q) ≤ duration t
    step t t∈P
      with find (toWitness (rel t (fromWitness t∈P)))
    ... | t' , t'∈Q , t'≼t =
          ≤-trans (bigMin-mem duration t' (traces Q) t'∈Q) (duration-≼ᶜ t'≼t)

-- the monoid structure is preserved: sequencing two grades adds their
-- best cases, the language product pairing each guarantee with each

mapₒ-· : (P Q : NeTraces) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀 (minSetDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

traces→left-sided-intervals : left-sided →ᵍ left-sided-intervals
traces→left-sided-intervals = record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-of-nat   = λ {n} → eq𝕀 (duration-⟨⟩ n)
  }

tracesToLeftSidedIntervalsGradeSystem : GradeSystem
tracesToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals
  ; EGrade = left-sided
  ; ∣_∣ᵉ   = traces→left-sided-intervals
  }
