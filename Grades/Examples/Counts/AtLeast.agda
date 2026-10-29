------------------------------------------------------------------------
-- Counts as lower bounds: "at least `k` of each operation".          --
--                                                                    --
-- A grade is one bound per counter; a computation is graded by it    --
-- when it has drawn on each counter at least that often. Sequencing  --
-- adds the counts, the order is `≥` on each counter, a smaller bound --
-- being the weaker grade, and the join is the pointwise minimum. The --
-- unit, demanding nothing, is the greatest grade.                    --
--                                                                    --
-- Each coordinate is the endpoint of a left-sided time interval, a   --
-- natural number; no point at infinity is needed.                    --
--                                                                    --
-- As a resource grade this is a guarantee: a token graded            --
-- `atleast 3` on a `heartbeat` counter is available once at least    --
-- three heartbeats have been performed.                              --
------------------------------------------------------------------------

module Grades.Examples.Counts.AtLeast where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁)

open import Relation.Binary.Definitions using (Minimum)
open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)

open import Grades.Examples.Time.LeftSided
  using (left-sided-intervals; left-sided-intervals-with-⊤; left-sided-intervalsʰ;
         left-sided-intervals-with-⊤ʰ;
         𝕀; [_,+∞⟩; uₒ-not-least; 𝕀⊤; timed_; untimed)

open import Grades.Examples.Counts.Power left-sided-intervals public

-- the grade over `n` counters

at-least-counts : ℕ → Grade ℕᴰ
at-least-counts = power

at-least-countsʰ : (n : ℕ) → GradeHints (at-least-counts n)
at-least-countsʰ = powerʰ left-sided-intervalsʰ

-- one coordinate

atleast : ℕ → 𝕀
atleast k = [ k ,+∞⟩

-- the unit is not least once there is a counter: demanding one more
-- of it lies strictly below demanding nothing

uᵛ-not-least : ∀ {n} → ¬ Minimum (_≾ᵛ_ {suc n}) uᵛ
uᵛ-not-least {n} least =
  uₒ-not-least (λ i → proj₁ (least (i ∷ uᵛ {n})))
  where open import Data.Vec.Base using (_∷_)

------------------------------------------------------------------------
-- The same counts with a formal greatest grade on each counter
--
-- The unit demands nothing and is greatest, but is not absorbing.
-- `untimed` on a counter makes no claim about it and is absorbing; the
-- grades whose greatest element is absorbing project to these counts.

import Grades.Examples.Counts.Power as Power
module WithTop = Power left-sided-intervals-with-⊤

at-least-counts-with-⊤ : ℕ → Grade ℕᴰ
at-least-counts-with-⊤ = WithTop.power

at-least-counts-with-⊤ʰ : (n : ℕ) → GradeHints (at-least-counts-with-⊤ n)
at-least-counts-with-⊤ʰ = WithTop.powerʰ left-sided-intervals-with-⊤ʰ

-- one coordinate

certainly : ℕ → 𝕀⊤
certainly k = timed [ k ,+∞⟩

no-claim : 𝕀⊤
no-claim = untimed
