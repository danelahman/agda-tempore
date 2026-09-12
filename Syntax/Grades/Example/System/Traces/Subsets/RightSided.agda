------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the subset grade of upper bounds: every run a      --
-- computation has is one of the listed traces. Resource grades are the --
-- right-sided time intervals, "at most `n` time steps".                --
--                                                                     --
--   ∣ Q ∣ᵉ  =  [0, the greatest duration among the traces of Q ]      --
--                                                                     --
-- The *greatest*, because the set is read disjunctively -- which run   --
-- occurs is not known, so the deadline has to cover the slowest. What  --
-- the resource grade forgets is which runs there were, so `⌈ write ⌉`  --
-- and `⟨ 3 ⟩` -- distinct grades upstream, and here incomparable, the  --
-- comparison between traces being equality -- become one deadline.     --
--                                                                     --
-- Monotonicity is immediate: weakening adds runs to the list, and a    --
-- longer list has a greater maximum.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.RightSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Subsets.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costʰⁱ : Op → ℕ) where

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

open import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_
  using (right-sided; _≾_)

open MaxDurations costʰⁱ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest listed run

mapₒ : NeTraces → 𝕀ᵣ
mapₒ Q = [0, setDuration (traces Q) ]

mapₒ-monotone : {P Q : NeTraces} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel = setDuration-⊑ (traces P) (traces Q) rel

-- the monoid structure is preserved: sequencing two grades adds their
-- worst cases, the language product pairing each run with each

mapₒ-· : (P Q : NeTraces) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀ᵣ (setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

subsets→right-sided-intervals : right-sided →ᵍ right-sided-intervals
subsets→right-sided-intervals = record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-of-nat   = λ {n} →
      eq𝕀ᵣ (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))
  }

subsetsToRightSidedIntervalsGradeSystem : GradeSystem
subsetsToRightSidedIntervalsGradeSystem = record
  { RGrade = right-sided-intervals
  ; EGrade = right-sided
  ; ∣_∣ᵉ   = subsets→right-sided-intervals
  }
