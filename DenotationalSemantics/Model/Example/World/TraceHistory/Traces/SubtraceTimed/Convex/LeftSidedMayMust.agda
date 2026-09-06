------------------------------------------------------------------------
-- A trace-history Kripke frame for the Convex.LeftSidedMayMust grade --
-- over the time-strict sub-trace order.                              --
--                                                                    --
-- `World.TraceHistory.Traces.Lifted.Convex.LeftSidedMayMust`, the    --
-- frame reached by appending a continuation that covers some demand  --
-- and takes every demand's time, at                                  --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay       --
-- only out of time the run spends in the same window -- between      --
-- the same two matched operations.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Convex.LeftSidedMayMust
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ c
  using (subtraceTimedOrder)
open import Syntax.Grades.Traces.SubtraceTimed.Duration Op c
  using () renaming (duration-≼ᵗ to duration-≼)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.Convex.LeftSidedMayMust
  Op _≟ₒ_ c subtraceTimedOrder duration-≼ public
