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
--                                                                     --
-- WHERE THE RESOURCE GRADES COME FROM. Not `Time.LeftSided` itself but --
-- `left-sided-intervals-with-⊤`. The floor's greatest grade demands    --
-- nothing and is absorbing -- forced, a top for the conjunctive subset --
-- order having to be included in every product -- while `[ 0 ,+∞⟩`,    --
-- the intervals' greatest grade, is their unit and so is not. No       --
-- monoid morphism at all can land in the plain intervals: `map-·` at   --
-- the absorbing top gives `map ⊤ ≡ map ⊤ · map c` for every `c`, and   --
-- at `c := of-nat 1` that reads `k ≡ k + 1` under `map-of-nat`, which   --
-- has no solution in ℕ. Adjoining a top to the target is what restores --
-- the projection, and it is the one place in the development where     --
-- that is needed -- every other endpoint is either read disjunctively  --
-- or bounded above.                                                    --
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
