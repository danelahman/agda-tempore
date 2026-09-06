------------------------------------------------------------------------
-- A trace-history Kripke frame for the Convex.LeftSidedMayMust grade --
-- over the lenient sub-trace order.                                  --
--                                                                    --
-- `World.TraceHistory.Traces.Lifted.Convex.LeftSidedMayMust`, the    --
-- frame reached by appending a continuation that covers some demand  --
-- and takes every demand's time, at                                  --
-- `Traces.Subtrace`'s `_≼_`, which lets time banked anywhere in a    --
-- run pay for a delay the demand places anywhere later.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.Convex.LeftSidedMayMust
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.Subtrace.AsOrder Op _≟ₒ_ c
  using (subtraceOrder)
open import Syntax.Grades.Traces.SubtraceDuration Op c
  using () renaming (duration-≼ to duration-≼)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.Convex.LeftSidedMayMust
  Op _≟ₒ_ c subtraceOrder duration-≼ public
