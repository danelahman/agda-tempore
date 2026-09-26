------------------------------------------------------------------------
-- Counts as upper bounds: "at most `k` of each operation".            --
--                                                                     --
-- A grade is one bound per counter, and a computation is graded by it --
-- when it draws on each counter at most that often. Sequencing adds   --
-- the counts, the order is `≤` on each, so a larger bound is the      --
-- weaker grade, and the join is the pointwise maximum. The unit, no   --
-- operations at all, is least.                                        --
--                                                                     --
-- Each coordinate is a right-sided time interval's endpoint, an       --
-- extended natural: `unlimited` on one counter lifts that quota and   --
-- keeps the others, and the greatest grade is `unlimited` on every    --
-- counter. A formal top of its own would lift every quota at once and --
-- nothing else; the extended naturals give the same greatest grade    --
-- and the partial quotas besides, with the order and the joins being  --
-- the product ones.                                                   --
--                                                                     --
-- As a resource grade this is a quota: a box graded `upto 3` on the   --
-- `send` counter may be opened by a computation that has sent at most --
-- three times, the shape of a rate limit.                             --
------------------------------------------------------------------------

module Syntax.Grades.Example.Counts.AtMost where

open import Data.Nat.Base using (ℕ)

open import Syntax.Grades using (Grade)

open import Syntax.Grades.Example.Time.RightSided
  using (right-sided-intervals; 𝕀ᵣ; [0,_]; ↑_; ∞)

open import Syntax.Grades.Example.Counts.Power right-sided-intervals public

-- the grade over `n` counters

at-most-counts : ℕ → Grade
at-most-counts = power

-- one coordinate

upto : ℕ → 𝕀ᵣ
upto k = [0, ↑ k ]

unlimited : 𝕀ᵣ
unlimited = [0, ∞ ]
