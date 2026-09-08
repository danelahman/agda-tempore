------------------------------------------------------------------------
-- A floor and a cap on sets of timed traces, Smyth-lifted from the   --
-- lenient sub-trace order.                                           --
--                                                                    --
-- `Example.Traces.Lifted.UpperLift.TwoSided` at                      --
-- `Traces.Subtrace`'s `_≼_`, which lets time banked anywhere in a    --
-- run pay for a delay the demand places anywhere later.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.Subtrace.UpperLift.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Subtrace.AsOrder Op _≟ₒ_ cost
  using (subtraceOrder)

open import Syntax.Grades.Example.Traces.Lifted.UpperLift.TwoSided
  Op _≟ₒ_ subtraceOrder public
