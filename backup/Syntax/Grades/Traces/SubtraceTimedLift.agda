------------------------------------------------------------------------
-- Lifting the time-strict sub-trace preorder to sets of timed traces. --
--                                                                     --
-- `Traces.OrderLift` at the time-strict order, giving the same two     --
-- lifts and the same laws as `Traces.SubtraceLift` does at the lenient --
-- one. What changes is which traces the lifts relate: a demand placing --
-- a delay between two of its operations is met only by a run that      --
-- spends the time between the *same* two, so the sets compared here    --
-- are compared window by window rather than in total.                  --
--                                                                     --
-- The grades over the two lifts are otherwise built identically, which --
-- is what the shared `OrderLift` records.                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.SubtraceTimedLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.SubtraceTimed.AsOrder Op _≟ₒ_ cost
  using (subtraceTimedOrder)

open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ subtraceTimedOrder public
