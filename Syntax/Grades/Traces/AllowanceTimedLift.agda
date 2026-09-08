------------------------------------------------------------------------
-- The set-level lifts of the time-strict allowance order.             --
--                                                                    --
-- `Traces.OrderLift` at `Traces.AllowanceTimed`'s `_≼ᵃᵗ_`, exactly as --
-- `Traces.AllowanceLift` is at the lenient one.                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.AllowanceTimedLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Syntax.Grades.Traces.AllowanceTimed.AsOrder Op _≟ₒ_ cost cost-pos
  using (allowanceTimedOrder)

open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ allowanceTimedOrder public
