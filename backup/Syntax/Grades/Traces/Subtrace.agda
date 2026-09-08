------------------------------------------------------------------------
-- A sub-trace preorder on timed traces, relative to a cost on         --
-- operation symbols.                                                  --
--                                                                     --
-- Operations come with a prescribed execution time: performing `o`     --
-- takes `cost o` units. A leading operation of the *left-hand* trace   --
-- may therefore be paid for out of the slack, at its execution time,   --
-- exactly as a leading delay is (`use-op` alongside `use-delay`). An   --
-- operation performed thus fits inside a pure time budget on the       --
-- right, `⌈ o ⌉ ≼ ⟨ n ⟩` as soon as `cost o ≤ n`.                     --
--                                                                     --
-- The converse never holds: slack is created only by absorbing the     --
-- *delays* of the right-hand trace (`del-delay`), and deleting one of  --
-- its operations (`del-op`) frees none. A right-hand trace that calls  --
-- for an operation is therefore not met by spending the same amount of --
-- time on anything else.                                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Traces.Subtrace (Op : Set) (cost : Op → ℕ) where

-- The relation itself, and its preorder structure: reflexivity at any
-- slack, weakening to more slack, and transitivity adding the slacks.

open import Syntax.Grades.Traces.Subtrace.Core Op cost public

-- The moves that lift the head-wise constructors to the trace
-- operations, up to monotonicity of the trace product.

open import Syntax.Grades.Traces.Subtrace.Moves Op cost public

-- The decision procedure, given decidable equality of operation names.

open import Syntax.Grades.Traces.Subtrace.Decidable Op cost public
