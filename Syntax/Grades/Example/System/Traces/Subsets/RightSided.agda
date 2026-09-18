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
--                                                                     --
-- The two grades' adjoined points correspond: `⊤ᵍ` permits any run at   --
-- all and `[0, ∞ ]` imposes no deadline, and both are absorbing.       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Data.Unit using (tt)

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
  using (right-sided; Permits; only_; ⊤ᵍ; _·ᵖ_; _≾_; _≾₀_)

open MaxDurations costʰⁱ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest listed run, and
-- the unrestricted grade by no deadline at all

mapₒ : Permits → 𝕀ᵣ
mapₒ (only Q) = [0, ↑ setDuration (traces Q) ]
mapₒ ⊤ᵍ       = [0, ∞ ]

mapₒ-monotone₀ : {P Q : NeTraces} → P ≾₀ Q
               → setDuration (traces P) ≤ setDuration (traces Q)
mapₒ-monotone₀ {P} {Q} rel = setDuration-⊑ (traces P) (traces Q) rel

mapₒ-monotone : {P Q : Permits} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {only P} {only Q} rel = mapₒ-monotone₀ {P} {Q} rel
mapₒ-monotone {only _} {⊤ᵍ}     rel = tt
mapₒ-monotone {⊤ᵍ}     {only _} ()
mapₒ-monotone {⊤ᵍ}     {⊤ᵍ}     rel = tt

-- the monoid structure is preserved: sequencing two grades adds their
-- worst cases, the language product pairing each run with each, and
-- both new points being absorbing

mapₒ-· : (P Q : Permits) → mapₒ (P ·ᵖ Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· (only P) (only Q) =
  eq𝕀ᵣ (cong ↑_ (setDuration-·ˢ (traces P) (traces Q)
                                (nonempty P) (nonempty Q)))
mapₒ-· (only _) ⊤ᵍ       = refl
mapₒ-· ⊤ᵍ       (only _) = refl
mapₒ-· ⊤ᵍ       ⊤ᵍ       = refl

subsets→right-sided-intervals : right-sided →ᵍ right-sided-intervals
subsets→right-sided-intervals = record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-⊤        = refl
  ; map-of-nat   = λ {n} →
      eq𝕀ᵣ (cong ↑_ (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n)))
  }

subsetsToRightSidedIntervalsGradeSystem : GradeSystem
subsetsToRightSidedIntervalsGradeSystem = record
  { RGrade = right-sided-intervals
  ; EGrade = right-sided
  ; ∣_∣ᵉ   = subsets→right-sided-intervals
  }
