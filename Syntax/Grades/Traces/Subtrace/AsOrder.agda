------------------------------------------------------------------------
-- The sub-trace preorder, packaged as a `TraceOrder`.                 --
--                                                                     --
-- Everything the grade construction asks of an order on traces, in the --
-- one place: the comparison and its decision procedure, the preorder   --
-- laws, monotonicity for the trace product, and the two facts about    --
-- the unit. Instantiating `Traces.OrderLift` here is what gives the    --
-- lenient order its set-level lifts.                                  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.Subtrace.AsOrder
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Order Op
open import Syntax.Grades.Traces.Subtrace Op cost
open import Syntax.Grades.Traces.SubtraceDuration Op cost using (≼-ε-inv)

open DecSubtrace _≟ₒ_ using (_≼?_)

subtraceOrder : TraceOrder
subtraceOrder = record
  { _≼_     = _≼_
  ; _≼?_    = _≼?_
  ; ≼-refl  = ≼-refl
  ; ≼-trans = ≼-trans
  ; ≼-nil   = nil
  ; mono-∙  = mono-∙
  ; ≼-ε-inv = ≼-ε-inv
  }
