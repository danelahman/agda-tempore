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
-- The target is `left-sided-intervals-with-⊤`: `no-demand` is         --
-- absorbing, `[ 0 ,+∞⟩` is not, and no monoid morphism bridges        --
-- the two.                                                            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Properties using (⊔-identityʳ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Syntax.Grades
open import Syntax.Grades.Example.Time.LeftSided

open import Util.Equality

module Syntax.Grades.Example.System.Traces.Subsets.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ : Op → ℕ) where

open import Data.Unit using (tt)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.MaxDuration Op _≟ₒ_

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using (left-sided; Demands; demanding_; no-demand; _·ᵈ_; _≾_; _≾₀_)

open MaxDurations costˡᵒ

------------------------------------------------------------------------
-- The projection: a grade is measured by its slowest demanded run, and
-- the grade demanding nothing by no claim about time at all

mapₒ : NeTraces → 𝕀
mapₒ P = [ setDuration (traces P) ,+∞⟩

mapₒ-monotone : {P Q : NeTraces} → P ≾₀ Q → mapₒ P ≾ₒ mapₒ Q
mapₒ-monotone {P} {Q} rel = setDuration-⊑ (traces Q) (traces P) rel

mapₒ-· : (P Q : NeTraces) → mapₒ (P · Q) ≡ mapₒ P ·ₒ mapₒ Q
mapₒ-· P Q =
  eq𝕀 (setDuration-·ˢ (traces P) (traces Q) (nonempty P) (nonempty Q))

mapₒ-of-nat : {n : ℕ} → mapₒ (of-nat n) ≡ [ n ,+∞⟩
mapₒ-of-nat {n} = eq𝕀 (trans (⊔-identityʳ (duration ⟨ n ⟩)) (duration-⟨⟩ n))

mapᵈ : Demands → 𝕀⊤
mapᵈ (demanding P) = timed (mapₒ P)
mapᵈ no-demand     = untimed

mapᵈ-monotone : {P Q : Demands} → P ≾ Q → mapᵈ P ≾ᵗ mapᵈ Q
mapᵈ-monotone {demanding P} {demanding Q} rel = mapₒ-monotone {P} {Q} rel
mapᵈ-monotone {demanding _} {no-demand}   rel = tt
mapᵈ-monotone {no-demand}   {demanding _} ()
mapᵈ-monotone {no-demand}   {no-demand}   rel = tt

mapᵈ-· : (P Q : Demands) → mapᵈ (P ·ᵈ Q) ≡ mapᵈ P ·ᵗ mapᵈ Q
mapᵈ-· (demanding P) (demanding Q) = cong timed_ (mapₒ-· P Q)
mapᵈ-· (demanding _) no-demand     = refl
mapᵈ-· no-demand     (demanding _) = refl
mapᵈ-· no-demand     no-demand     = refl

subsets→left-sided-intervals : left-sided →ᵍ left-sided-intervals-with-⊤
subsets→left-sided-intervals = record
  { map          = mapᵈ
  ; map-monotone = λ {P} {Q} → mapᵈ-monotone {P} {Q}
  ; map-u        = refl
  ; map-·        = λ {P} {Q} → mapᵈ-· P Q
  ; map-⊤        = refl
  ; map-of-nat   = λ {n} → cong timed_ (mapₒ-of-nat {n})
  }

subsetsToLeftSidedIntervalsGradeSystem : GradeSystem
subsetsToLeftSidedIntervalsGradeSystem = record
  { RGrade = left-sided-intervals-with-⊤
  ; EGrade = left-sided
  ; ∣_∣ᵉ   = subsets→left-sided-intervals
  }
