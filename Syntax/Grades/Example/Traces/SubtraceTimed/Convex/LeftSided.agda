------------------------------------------------------------------------
-- A floor on sets of timed traces, convexly lifted from the          --
-- time-strict sub-trace order.                                       --
--                                                                    --
-- `Example.Traces.Lifted.Convex.LeftSided` at                        --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay       --
-- only out of time the run spends in the same window -- between      --
-- the same two matched operations.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.SubtraceTimed.Convex.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ cost
  using (subtraceTimedOrder)

open import Syntax.Grades.Example.Traces.Lifted.Convex.LeftSided
  Op _≟ₒ_ subtraceTimedOrder public
