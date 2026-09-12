------------------------------------------------------------------------
-- The set-level lifts of the coverage order.                          --
--                                                                    --
-- `Traces.OrderLift` at `Traces.Coverage`'s `_≼ᶜ_`, giving the Hoare  --
-- lower lift and the Smyth upper lift of it, with their preorder      --
-- laws, monotonicity for the language product, how each sits against  --
-- the unit `{ ε }`, and the decision procedures.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.CoverageLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Coverage.AsOrder Op _≟ₒ_ costˡᵒ
  using (coverageOrder)

open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ coverageOrder public
