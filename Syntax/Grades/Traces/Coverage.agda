------------------------------------------------------------------------
-- A coverage order on timed traces, relative to a cost on operation   --
-- symbols.                                                            --
--                                                                    --
-- `s ≼ᶜ t` reads: the run `t` covers the trace `s`. Every operation   --
-- `s` names must genuinely occur in `t`, in order -- time never buys  --
-- one -- and every delay `s` names must be covered by what `t` does   --
-- between the same two operations it names, unmatched operations      --
-- counting at their execution time. So `⟨ n ⟩ ≼ᶜ t` as soon as `t`    --
-- spends `n` where `s` asks for it, and `⌈ o ⌉ ≼ᶜ t` only when `t`    --
-- performs `o`.                                                       --
--                                                                    --
-- This is the order a *guarantee* wants, and it is not the converse   --
-- of `Traces.Allowance`: there a bound's delays buy the run's         --
-- operations, which read as a guarantee would let a run that merely   --
-- idles discharge "a reading was taken".                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Traces.Coverage (Op : Set) (cost : Op → ℕ) where

-- The relation itself, and its preorder structure: reflexivity at any
-- slack, weakening to more slack, and transitivity adding the slacks.

open import Syntax.Grades.Traces.Coverage.Core Op cost public

-- The moves, with monotonicity of the trace product in its pinned form.

open import Syntax.Grades.Traces.Coverage.Moves Op cost public

-- How the order bounds durations, and what a spent run covers.

open import Syntax.Grades.Traces.Coverage.Duration Op cost public

-- The decision procedure, given decidable equality of operation names.

open import Syntax.Grades.Traces.Coverage.Decidable Op cost public
