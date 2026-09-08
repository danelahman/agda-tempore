------------------------------------------------------------------------
-- A trace-history Kripke frame for the Mixed.TwoSided grade over the  --
-- time-strict sub-trace order.                                        --
--                                                                    --
-- `World.TraceHistory.Traces.Lifted.Mixed.TwoSided`, the frame        --
-- reached by appending a continuation that covers one listed demand   --
-- and stays within one listed allowance, at                           --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay only   --
-- out of time the run spends in the same window -- between the same   --
-- two matched operations.                                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Mixed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ c
  using (subtraceTimedOrder)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.Mixed.TwoSided
  Op _≟ₒ_ subtraceTimedOrder public
