------------------------------------------------------------------------
-- Sets of timed traces as upper bounds, at the time-strict allowance  --
-- order.                                                              --
--                                                                    --
-- `Example.Traces.Lifted.RightSided` at                               --
-- `Traces.AllowanceTimed`'s `_≼ᵃᵗ_`: as above, except that the        --
-- bound's budget is available only where the bound says it is, so a   --
-- run's unnamed work must be covered between the same two operations  --
-- the bound names it between.                                        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.AllowanceTimed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Syntax.Grades.Traces.AllowanceTimed.AsOrder Op _≟ₒ_ cost cost-pos
  using (allowanceTimedOrder)

open import Syntax.Grades.Example.Traces.Lifted.RightSided
  Op _≟ₒ_ allowanceTimedOrder public
