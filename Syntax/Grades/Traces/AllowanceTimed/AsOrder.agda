------------------------------------------------------------------------
-- The time-strict allowance preorder, packaged as a `TraceOrder`.     --
--                                                                    --
-- The same interface `Allowance.AsOrder` meets, at the restricted     --
-- order. `mono-∙` is available only with the second budget pinned to  --
-- zero -- the budget-additive form is false here, as                  --
-- `AllowanceTimed.Moves` records -- but the lift is taken at budget   --
-- zero throughout, so that is exactly the instance needed. `≼-ε-inv`  --
-- is inherited through the embedding into the lenient order.          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.AllowanceTimed.AsOrder
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Syntax.Grades.Traces.Order Op
open import Syntax.Grades.Traces.AllowanceTimed Op cost

open DecAllowanceTimed _≟ₒ_ using (_≼ᵃᵗ?_)

allowanceTimedOrder : TraceOrder
allowanceTimedOrder = record
  { _≼_     = _≼ᵃᵗ_
  ; _≼?_    = _≼ᵃᵗ?_
  ; ≼-refl  = ≼ᵃᵗ-refl
  ; ≼-trans = ≼ᵃᵗ-trans
  ; ≼-nil   = nil
  ; mono-∙  = mono-∙
  ; ≼-ε-inv = ≼ᵃᵗ-ε-inv cost-pos
  }
