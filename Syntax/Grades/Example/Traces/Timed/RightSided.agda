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
--                                                                     --
-- A bound charges an operation `costʰⁱ`, the most time it can take.    --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Syntax.Grades.Traces.Allowance.AsOrder Op _≟ₒ_ costʰⁱ costʰⁱ-pos
  using (allowanceOrder)

open import Syntax.Grades.Example.Traces.Lifted.RightSided
  Op _≟ₒ_ allowanceOrder public
