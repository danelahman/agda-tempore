------------------------------------------------------------------------
-- Sets of timed traces as upper bounds, at the allowance order.       --
--                                                                    --
-- `Example.Traces.Lifted.RightSided` at `Traces.Allowance`'s `_≼ᵃ_`.  --
-- A grade lists bounds, and a run stays within one of them when the   --
-- bound names every operation the run performs, or leaves enough      --
-- budget to cover the ones it does not, and enough for the run's own  --
-- idling. Budget is local: what the bound offers between two          --
-- operations it names pays only for what the run does between those   --
-- same two, so a bound says when its slack is available.              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.Allowance.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Syntax.Grades.Traces.Allowance.AsOrder Op _≟ₒ_ cost cost-pos
  using (allowanceOrder)

open import Syntax.Grades.Example.Traces.Lifted.RightSided
  Op _≟ₒ_ allowanceOrder public
