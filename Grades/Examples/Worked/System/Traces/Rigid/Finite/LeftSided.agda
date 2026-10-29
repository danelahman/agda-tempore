------------------------------------------------------------------------
-- Worked instance: rigid finite-expression lower bounds, measured by --
-- the fastest run.                                                   --
--                                                                    --
-- `System.Traces.Rigid.Finite.LeftSided` measures a lower bound by   --
-- the infimum of the durations of its runs. Heating takes two to     --
-- four units, cooling more than one and less than two, logging more  --
-- than a quarter and at most a half. Each measure is computed.       --
------------------------------------------------------------------------

module Grades.Examples.Worked.System.Traces.Rigid.Finite.LeftSided where

open import Data.Bool.Base using (true; false)

open import Util.Equality

open import Grades.Base using (_→ᵍ_)
open _→ᵍ_ using (map)

open import Grades.Examples.Time.Dense.LeftSided using ([_,+∞⟩; _/_; #_)
open import Grades.Examples.Worked.Traces.Rigid.Finite.Operations
open import Grades.Examples.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running
open import Grades.Examples.System.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running
  using (lower-runs→left-sided-intervals)

∣_∣ = map lower-runs→left-sided-intervals

-- heating, an undisturbed wait of at least one, logging: at least three
-- and a quarter units, the open end of logging closed

heat-wait-log : ∣ ⌜ ‵ heat · idle ≥ (# 1) · ‵ log ⌝ ∣ ≡ [ 13 / 4 ,+∞⟩
heat-wait-log = refl

-- flanks of activity add nothing to the least duration

flanked : ∣ ⌜ ≥ (# 0) · ‵ cool · ≥ (# 0) ⌝ ∣ ≡ [ # 1 ,+∞⟩
flanked = refl

-- a choice is measured by its faster branch

heat-or-cool : ∣ ⌜ ‵ heat ∣ ‵ cool ⌝ ∣ ≡ [ # 1 ,+∞⟩
heat-or-cool = refl

-- a guarantee of more than a unit and one of at least a unit are
-- measured alike, though only the second admits a unit exactly

open-closed : ∣ ⌜ > (# 1) ⌝ ∣ ≡ ∣ ⌜ ≥ (# 1) ⌝ ∣
open-closed = refl

closed-not-below-open : holds ⌜ ≥ (# 1) ⌝ ⌜ > (# 1) ⌝ ≡ false
closed-not-below-open = refl
