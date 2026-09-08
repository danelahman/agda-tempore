------------------------------------------------------------------------
-- The time-strict sub-trace preorder, packaged as a `TraceOrder`.     --
--                                                                     --
-- The same interface `Subtrace.AsOrder` meets, at the restricted       --
-- order. Two fields are worth noting.                                  --
--                                                                     --
-- `mono-∙` is available only in the form with the second slack pinned  --
-- to zero -- the slack-additive form is false here, as                 --
-- `SubtraceTimed.Moves` records -- but the lift is taken at slack zero --
-- throughout, so that is exactly the instance needed.                  --
--                                                                     --
-- `≼-ε-inv` is inherited: the time-strict order embeds in the lenient  --
-- one, so a demand it puts below `ε` is one the lenient order does.    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.SubtraceTimed.AsOrder
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Order Op
open import Syntax.Grades.Traces.SubtraceTimed Op cost

open DecSubtraceTimed _≟ₒ_ using (_≼ᵗ?_)

subtraceTimedOrder : TraceOrder
subtraceTimedOrder = record
  { _≼_     = _≼ᵗ_
  ; _≼?_    = _≼ᵗ?_
  ; ≼-refl  = ≼ᵗ-refl
  ; ≼-trans = ≼ᵗ-trans
  ; ≼-nil   = nil
  ; mono-∙  = mono-∙
  ; ≼-ε-inv = ≼ᵗ-ε-inv
  }
