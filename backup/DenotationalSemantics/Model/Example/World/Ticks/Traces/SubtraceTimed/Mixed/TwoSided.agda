------------------------------------------------------------------------
-- A time-ticks Kripke frame for the Mixed.TwoSided grade over the     --
-- time-strict sub-trace order.                                        --
--                                                                    --
-- `World.Ticks.Traces.Lifted.Mixed.TwoSided`, the frame reached by    --
-- advancing past one listed demand and no further than one listed     --
-- allowance, at `Traces.SubtraceTimed`'s `_≼ᵗ_`, which pays a         --
-- demanded delay only out of time the run spends in the same window   --
-- -- between the same two matched operations.                         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.Mixed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ c
  using (subtraceTimedOrder)
open import Syntax.Grades.Traces.SubtraceTimed.Duration Op c
  using () renaming (duration-≼ᵗ to duration-≼)

open import DenotationalSemantics.Model.Example.World.Ticks.Traces.Lifted.Mixed.TwoSided
  Op _≟ₒ_ c subtraceTimedOrder duration-≼ public
