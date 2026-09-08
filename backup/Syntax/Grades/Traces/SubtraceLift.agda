------------------------------------------------------------------------
-- Lifting the sub-trace preorder to sets of timed traces.             --
--                                                                     --
-- `Traces.OrderLift` at the lenient sub-trace order, which supplies    --
--                                                                     --
--   xs ≼ˢ ys   every trace of `xs` fits inside some trace of `ys`     --
--   xs ≽ˢ ys   every trace of `ys` has some trace of `xs` inside it   --
--                                                                     --
-- together with their preorder laws, monotonicity for the language     --
-- product, how each sits against the unit `{ ε }`, and the decision    --
-- procedures. Since time banked anywhere in the run pays for a delay   --
-- demanded anywhere later, a set compared here is compared up to that  --
-- freedom; `Traces.SubtraceTimedLift` is the same lift taken over the  --
-- order that refuses it.                                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.SubtraceLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Subtrace.AsOrder Op _≟ₒ_ cost
  using (subtraceOrder)

open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ subtraceOrder public
