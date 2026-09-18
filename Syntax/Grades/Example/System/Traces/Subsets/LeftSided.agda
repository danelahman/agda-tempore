------------------------------------------------------------------------
-- A grade system in which the resource grades measure only time.      --
--                                                                     --
-- Effect grades are the subset grade of lower bounds: each listed run --
-- is one the computation can still exhibit. Resource grades are the   --
-- left-sided time intervals, "at least `n` time steps".               --
--                                                                     --
--   ∣ P ∣ᵉ  =  [ the greatest duration among the traces of P ,+∞⟩     --
--                                                                     --
-- The set is read conjunctively, so the guarantee is the slowest run; --
-- `System.Traces.Timed.LeftSided` reads its floor disjunctively and   --
-- takes the fastest.                                                  --
--                                                                     --
-- Monotonicity: weakening drops listed runs, and a shorter list has a --
-- smaller maximum, so the guarantee falls.                            --
--                                                                     --
-- The target is `left-sided-intervals-with-⊤`, not the plain          --
-- intervals: the floor's top is absorbing, theirs is the unit, and no --
-- monoid morphism bridges the two.                                    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.WithTop
open import Syntax.Grades.Example.Time.LeftSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Subsets.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; base; _≾₀_)

open MaxDurations costˡᵒ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest demanded run
--
-- Stated on the sets alone; the two adjoined tops are matched up by the
-- generic extension of a morphism, which sends one to the other.

mapₒ : NeTraces → 𝕀
mapₒ P = [ setDuration (traces P) ,+∞⟩

mapₒ-monotone : {P Q : NeTraces} → P ≾₀ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel = setDuration-⊑ (traces Q) (traces P) rel

mapₒ-· : (P Q : NeTraces) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀 (setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

mapₒ-of-nat : {n : ℕ} → mapₒ (of-nat n) ≡ [ n ,+∞⟩
mapₒ-of-nat {n} = eq𝕀 (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))

open AdjoinMap {base} {forgetTop left-sided-intervals}
  mapₒ (λ {P} {Q} → mapₒ-monotone {P} {Q}) refl (λ {P} {Q} → mapₒ-· P Q)
  (λ {n} → mapₒ-of-nat {n})
  public using () renaming (withTopᵐ to subsets→left-sided-intervals)

subsetsToLeftSidedIntervalsGradeSystem : GradeSystem
subsetsToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals-with-⊤
  ; EGrade = left-sided
  ; ∣_∣ᵉ   = subsets→left-sided-intervals
  }
