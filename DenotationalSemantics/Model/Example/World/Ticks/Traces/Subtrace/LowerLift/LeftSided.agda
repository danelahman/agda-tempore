------------------------------------------------------------------------
-- A time-ticks Kripke frame for the LowerLift.LeftSided grade over   --
-- the lenient sub-trace order.                                       --
--                                                                    --
-- `World.Ticks.Traces.Lifted.LowerLift.LeftSided`, the frame reached --
-- by advancing past every listed demand's duration, at               --
-- `Traces.Subtrace`'s `_≼_`, which lets time banked anywhere in a    --
-- run pay for a delay the demand places anywhere later.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.Ticks.Traces.Subtrace.LowerLift.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.Subtrace.AsOrder Op _≟ₒ_ c
  using (subtraceOrder)
open import Syntax.Grades.Traces.SubtraceDuration Op c
  using () renaming (duration-≼ to duration-≼)

open import DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.LowerLift.LeftSided
  Op _≟ₒ_ c subtraceOrder duration-≼ public
