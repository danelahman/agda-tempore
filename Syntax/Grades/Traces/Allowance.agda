------------------------------------------------------------------------
-- An allowance order on timed traces, relative to a `costʰⁱ` on       --
-- operation symbols.                                                  --
--                                                                    --
-- `s ≼ᵃ t` reads: the bound `t` permits the run `s`. Its operations   --
-- are permissions -- an operation the bound names may be performed,   --
-- and one it does not name may still be performed if the bound's      --
-- delays leave enough time to cover its execution cost. Its delays    --
-- are a budget, which the run's own idling draws on as well.          --
--                                                                    --
-- Going up the order, an operation turns into a delay long enough to  --
-- cover it and a delay grows: `⌈ o ⌉ ≼ᵃ ⟨ n ⟩` as soon as             --
-- `costʰⁱ o ≤ n`, and `⟨ m ⟩ ≼ᵃ ⟨ n ⟩` as soon as `m ≤ n`. What does  --
-- *not* happen is the converse: an operation the bound names but the  --
-- run skips frees no budget, so a bound is an upper bound on which    --
-- effects occur as well as on how long they take.                     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Traces.Allowance (Op : Set) (costʰⁱ : Op → ℕ) where

-- The relation itself, and its preorder structure: reflexivity at any
-- budget, weakening to more budget, and transitivity adding the
-- budgets.

open import Syntax.Grades.Traces.Allowance.Core Op costʰⁱ public

-- The moves that lift the head-wise rules to the trace operations, up
-- to monotonicity of the trace product.

open import Syntax.Grades.Traces.Allowance.Moves Op costʰⁱ public

-- How the order bounds durations, and what the empty bound permits.

open import Syntax.Grades.Traces.Allowance.Duration Op costʰⁱ public

-- The decision procedure, given decidable equality of operation names.

open import Syntax.Grades.Traces.Allowance.Decidable Op costʰⁱ public
