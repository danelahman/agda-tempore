------------------------------------------------------------------------
-- A time-ticks Kripke frame for the LowerLift.TwoSided grade over the--
-- time-strict sub-trace order.                                       --
--                                                                    --
-- `World.Ticks.Traces.Lifted.LowerLift.TwoSided`, the frame reached  --
-- by advancing between the two endpoints' durations, at              --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay       --
-- only out of time the run spends in the same window -- between      --
-- the same two matched operations.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.LowerLift.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ c
  using (subtraceTimedOrder)
open import Syntax.Grades.Traces.SubtraceTimed.Duration Op c
  using () renaming (duration-≼ᵗ to duration-≼)

open import DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.LowerLift.TwoSided
  Op _≟ₒ_ c subtraceTimedOrder duration-≼ public
