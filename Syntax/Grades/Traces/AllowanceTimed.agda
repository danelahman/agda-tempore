------------------------------------------------------------------------
-- The time-strict allowance order on timed traces.                    --
--                                                                    --
-- `Traces.Allowance` with one rule changed: an operation matched      --
-- against the bound does not carry budget across it. So the work a    --
-- run does between two operations the bound names is paid for only by --
-- what the bound offers between the same two, and a bound may say     --
-- *when* its budget is available and not merely how much of it there  --
-- is.                                                                 --
--                                                                    --
-- Every time-strict derivation is an allowance derivation             --
-- (`≼ᵃᵗ→≼ᵃ`), so this order is finer: fewer runs are permitted.       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Traces.AllowanceTimed (Op : Set) (cost : Op → ℕ) where

-- The relation, its preorder structure, and the embedding into the
-- lenient order.

open import Syntax.Grades.Traces.AllowanceTimed.Core Op cost public

-- The moves, with monotonicity of the trace product in its pinned form.

open import Syntax.Grades.Traces.AllowanceTimed.Moves Op cost public

-- Durations and the empty bound, inherited through the embedding.

open import Syntax.Grades.Traces.AllowanceTimed.Duration Op cost public

-- The decision procedure.

open import Syntax.Grades.Traces.AllowanceTimed.Decidable Op cost public
