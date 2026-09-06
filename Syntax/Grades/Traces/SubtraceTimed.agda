------------------------------------------------------------------------
-- The time-strict sub-trace preorder on timed traces.                 --
--                                                                     --
-- `Traces.Subtrace`'s `_≼_` banks time globally: a delay the demand    --
-- places anywhere may be paid for by time the run spends anywhere      --
-- earlier. This relation refuses to carry banked time across a matched --
-- operation, so a demanded delay must be paid for within the window    --
-- the demand puts it in -- between the same two operations.            --
--                                                                     --
-- Otherwise the two orders are the same, and `Core`'s `≼ᵗ→≼` records   --
-- that this one is a restriction of the other.                        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

module Syntax.Grades.Traces.SubtraceTimed (Op : Set) (cost : Op → ℕ) where

-- The relation itself, its preorder structure, and the embedding into
-- the lenient sub-trace preorder.

open import Syntax.Grades.Traces.SubtraceTimed.Core Op cost public

-- The moves that lift the head-wise constructors to the trace
-- operations, up to monotonicity of the trace product.

open import Syntax.Grades.Traces.SubtraceTimed.Moves Op cost public

-- Durations along the order, and what it says about demanded time.

open import Syntax.Grades.Traces.SubtraceTimed.Duration Op cost public

-- The decision procedure, given decidable equality of operation names.

open import Syntax.Grades.Traces.SubtraceTimed.Decidable Op cost public
