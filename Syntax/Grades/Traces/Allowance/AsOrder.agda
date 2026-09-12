------------------------------------------------------------------------
-- The allowance preorder, packaged as a `TraceOrder`.                 --
--                                                                    --
-- Everything the grade construction asks of an order on traces, in    --
-- one place: the comparison and its decision procedure, the preorder  --
-- laws, monotonicity for the trace product, and the two facts about   --
-- the unit.                                                          --
--                                                                    --
-- Positivity of `costʰⁱ` is a parameter here rather than a hypothesis --
-- carried around: it is what makes the empty bound permit nothing but --
-- the empty run, and so what the grades' zero-product law rests on.   --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.Allowance.AsOrder
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Syntax.Grades.Traces.Order Op
open import Syntax.Grades.Traces.Allowance Op costʰⁱ

open DecAllowance _≟ₒ_ using (_≼ᵃ?_)

allowanceOrder : TraceOrder
allowanceOrder = record
  { _≼_     = _≼ᵃ_
  ; _≼?_    = _≼ᵃ?_
  ; ≼-refl  = ≼ᵃ-refl
  ; ≼-trans = ≼ᵃ-trans
  ; ≼-nil   = nil
  ; mono-∙  = mono-∙
  ; ≼-ε-inv = ≼ᵃ-ε-inv costʰⁱ-pos
  }
