------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the subset grade of lower bounds: each listed run  --
-- is one the computation can still exhibit. Resource grades are the    --
-- left-sided time intervals, "at least `n` time steps".                --
--                                                                     --
--   ∣ P ∣ᵉ  =  [ the greatest duration among the traces of P ,+∞⟩     --
--                                                                     --
-- The *greatest*, and this is the one place where the two families     --
-- disagree about which end of a set to read. Here the set is a         --
-- conjunction of demands -- every listed run must remain reachable --   --
-- so what the grade guarantees about time is what the slowest of them  --
-- takes. `System.Traces.Timed.LeftSided` reads its floor               --
-- disjunctively and so takes the fastest instead. Same target grade,   --
-- opposite aggregation, because the sets are read differently.         --
--                                                                     --
-- This is also exactly what the tick frame of                          --
-- `Ticks.Traces.Subsets.LeftSided` sees, its condition being universal --
-- in the listed runs.                                                  --
--                                                                     --
-- Monotonicity: weakening drops listed runs, and a shorter list has a  --
-- smaller maximum, so the guarantee falls.                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.LeftSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Subsets.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; _≾_)

open MaxDurations costˡᵒ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest demanded run

mapₒ : NeTraces → 𝕀
mapₒ P = [ setDuration (traces P) ,+∞⟩

mapₒ-monotone : {P Q : NeTraces} → P ≾ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel = setDuration-⊑ (traces Q) (traces P) rel

mapₒ-· : (P Q : NeTraces) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀 (setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

subsets→left-sided-intervals : left-sided →ᵍ left-sided-intervals
subsets→left-sided-intervals = record
  { map          = mapₒ
  ; map-monotone = λ {P} {Q} → mapₒ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapₒ-· P Q
  ; map-of-nat   = λ {n} →
      eq𝕀 (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))
  }

subsetsToLeftSidedIntervalsGradeSystem : GradeSystem
subsetsToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals
  ; EGrade = left-sided
  ; ∣_∣ᵉ   = subsets→left-sided-intervals
  }
