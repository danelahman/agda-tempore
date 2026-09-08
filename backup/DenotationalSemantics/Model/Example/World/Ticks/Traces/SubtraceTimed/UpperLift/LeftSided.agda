------------------------------------------------------------------------
-- A time-ticks Kripke frame for the UpperLift.LeftSided grade over   --
-- the time-strict sub-trace order.                                   --
--                                                                    --
-- `World.Ticks.Traces.Lifted.UpperLift.LeftSided`, the frame reached --
-- by advancing past some listed demand's duration, at                --
-- `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a demanded delay       --
-- only out of time the run spends in the same window -- between      --
-- the same two matched operations.                                   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.UpperLift.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ c
  using (subtraceTimedOrder)
open import Syntax.Grades.Traces.SubtraceTimed.Duration Op c
  using () renaming (duration-≼ᵗ to duration-≼)

open import DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.UpperLift.LeftSided
  Op _≟ₒ_ c subtraceTimedOrder duration-≼ public
