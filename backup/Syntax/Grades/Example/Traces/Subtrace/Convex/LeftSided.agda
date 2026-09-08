------------------------------------------------------------------------
-- A floor on sets of timed traces, convexly lifted from the          --
-- lenient sub-trace order.                                           --
--                                                                    --
-- `Example.Traces.Lifted.Convex.LeftSided` at                        --
-- `Traces.Subtrace`'s `_≼_`, which lets time banked anywhere in a    --
-- run pay for a delay the demand places anywhere later.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.Subtrace.Convex.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Subtrace.AsOrder Op _≟ₒ_ cost
  using (subtraceOrder)

open import Syntax.Grades.Example.Traces.Lifted.Convex.LeftSided
  Op _≟ₒ_ subtraceOrder public
