------------------------------------------------------------------------
-- Worked instance: rigid finite-expression upper bounds, measured by --
-- the slowest run.                                                   --
--                                                                    --
-- `System.Traces.Rigid.Finite.RightSided` measures an upper bound by --
-- the supremum of the durations of its runs. Heating takes two to    --
-- four units, cooling more than one and less than two, logging more  --
-- than a quarter and at most a half. Each measure is computed.       --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.Rigid.Finite.RightSided where

open import Data.Bool.Base using (true)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)
open _→ᵍ_ using (map)

open import Grades.Examples.Time.Dense.RightSided using ([0,_]; ↑_; ∞; _/_; #_)
open import Grades.Examples.Worked.Traces.Rigid.Finite.Operations
open import Grades.Examples.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running
open import Grades.Examples.System.Traces.Rigid.Finite.RightSided Op 3 code name name-code code-name running
  using (upper-runs→right-sided-intervals)

∣_∣ = map upper-runs→right-sided-intervals

-- heating, less than a unit of anything, logging: at most five and a
-- half units, the open end of the budget closed

heat-wait-log : ∣ ⌜ ‵ heat · < (# 1) · ‵ log ⌝ ∣ ≡ [0, ↑ 11 / 2 ]
heat-wait-log = refl

-- cooling takes less than two units, measured two

cool-measured : ∣ ⌜ ‵ cool ⌝ ∣ ≡ [0, ↑ # 2 ]
cool-measured = refl

-- a choice is measured by its slower branch

heat-or-cool : ∣ ⌜ ‵ heat ∣ ‵ cool ⌝ ∣ ≡ [0, ↑ # 4 ]
heat-or-cool = refl

-- an unbounded stretch imposes no deadline

unbounded : ∣ ⌜ ‵ log · ≤∞ ⌝ ∣ ≡ [0, ∞ ]
unbounded = refl

-- monotonicity: cooling fits a budget of less than two, and the two
-- deadlines agree, the open end being closed by the measure

cool-in-budget : holds ⌜ ‵ cool ⌝ ⌜ < (# 2) ⌝ ≡ true
cool-in-budget = refl

budget-measured : ∣ ⌜ < (# 2) ⌝ ∣ ≡ ∣ ⌜ ‵ cool ⌝ ∣
budget-measured = refl
