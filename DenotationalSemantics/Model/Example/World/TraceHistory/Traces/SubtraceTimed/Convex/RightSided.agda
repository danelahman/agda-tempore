------------------------------------------------------------------------
-- A trace-history Kripke frame for the Convex.RightSided grade over  --
-- the time-strict sub-trace order.                                   --
--                                                                    --
-- `World.TraceHistory.Traces.Lifted.Convex.RightSided`, the frame    --
-- reached by appending a continuation that stays within a listed     --
-- allowance, at                                                      --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay       --
-- only out of time the run spends in the same window -- between      --
-- the same two matched operations.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Convex.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ c
  using (subtraceTimedOrder)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.Convex.RightSided
  Op _≟ₒ_ subtraceTimedOrder public
