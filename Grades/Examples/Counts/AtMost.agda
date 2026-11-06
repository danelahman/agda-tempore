------------------------------------------------------------------------
-- At-most counts: "at most `k` of each operation".                   --
--                                                                    --
-- A grade is one bound per counter; a computation is graded by it    --
-- when it draws on each counter at most that often. Sequencing adds  --
-- the counts, the order is `≤` on each counter, a larger bound being --
-- the weaker grade, and the join is the pointwise maximum. The unit, --
-- no operations at all, is least.                                    --
--                                                                    --
-- Each coordinate is the endpoint of an upper bound on time, an      --
-- extended natural number: `unlimited` on one counter lifts that     --
-- quota and keeps the others, and the greatest grade is `unlimited`  --
-- on every counter. The order and the joins are those of the         --
-- product.                                                           --
--                                                                    --
-- As a resource grade this is a quota: a box graded `upto 3` on the  --
-- `send` counter may be opened by a computation that has sent at     --
-- most three times, as in a rate limit.                              --
------------------------------------------------------------------------

module Grades.Examples.Counts.AtMost where

open import Data.Nat.Base using (ℕ)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)

open import Grades.Examples.Time.UpperBound
  using (upper-bounds; upper-boundsʰ; 𝕀ᵣ; [0,_]; ↑_; ∞)

open import Grades.Examples.Counts.Power upper-bounds public

-- the grade over `n` counters

at-most-counts : ℕ → Grade ℕᴰ
at-most-counts = power

at-most-countsʰ : (n : ℕ) → GradeHints (at-most-counts n)
at-most-countsʰ = powerʰ upper-boundsʰ

-- one coordinate

upto : ℕ → 𝕀ᵣ
upto k = [0, ↑ k ]

unlimited : 𝕀ᵣ
unlimited = [0, ∞ ]
