------------------------------------------------------------------------
-- A trace-history Kripke frame for the LowerLift.RightSided grade    --
-- over the lenient sub-trace order.                                  --
--                                                                    --
-- `World.TraceHistory.Traces.Lifted.LowerLift.RightSided`, the frame --
-- reached by appending a continuation that stays within a listed     --
-- allowance, at                                                      --
-- `Traces.Subtrace`'s `_≼_`, which lets time banked anywhere in a    --
-- run pay for a delay the demand places anywhere later.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.LowerLift.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.Subtrace.AsOrder Op _≟ₒ_ c
  using (subtraceOrder)

open import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Lifted.LowerLift.RightSided
  Op _≟ₒ_ subtraceOrder public
