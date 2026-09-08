------------------------------------------------------------------------
-- The set-level lifts of the allowance order.                         --
--                                                                    --
-- `Traces.OrderLift` at `Traces.Allowance`'s `_≼ᵃ_`, giving the Hoare --
-- lower lift and the Smyth upper lift of it, with their preorder      --
-- laws, monotonicity for the language product, how each sits against  --
-- the unit `{ ε }`, and the decision procedures.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.AllowanceLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Syntax.Grades.Traces.Allowance.AsOrder Op _≟ₒ_ cost cost-pos
  using (allowanceOrder)

open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ allowanceOrder public
