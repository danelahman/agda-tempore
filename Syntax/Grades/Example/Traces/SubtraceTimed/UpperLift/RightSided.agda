------------------------------------------------------------------------
-- A cap on sets of timed traces, Smyth-lifted from the               --
-- time-strict sub-trace order.                                       --
--                                                                    --
-- `Example.Traces.Lifted.UpperLift.RightSided` at                    --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay       --
-- only out of time the run spends in the same window -- between      --
-- the same two matched operations.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ cost
  using (subtraceTimedOrder)

open import Syntax.Grades.Example.Traces.Lifted.UpperLift.RightSided
  Op _≟ₒ_ subtraceTimedOrder public
