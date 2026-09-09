------------------------------------------------------------------------
-- Two-sided trace intervals: a coverage floor under an allowance cap. --
--                                                                    --
-- `Example.Traces.Lifted.TwoSided` at the two orders the two          --
-- endpoints want -- `Traces.Coverage`'s `_≼ᶜ_` below and              --
-- `Traces.Allowance`'s `_≼ᵃ_` above. A grade `[ P , Q ]` says:        --
--                                                                    --
--   whatever the computation did, it covered one of the traces in `P` --
--   and stayed within one of the traces in `Q`                        --
--                                                                    --
-- with both sets read disjunctively, so both weaken by gaining        --
-- members. `Example.Traces.Timed.LeftSided` and                    --
-- `Example.Traces.Timed.RightSided` are its two endpoints read    --
-- alone.                                                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ)
  (cost-pos : (o : Op) → 0 < cost o) where

open import Syntax.Grades.Traces.Coverage.AsOrder Op _≟ₒ_ cost
  using (coverageOrder)
open import Syntax.Grades.Traces.Coverage Op cost using (duration-≼ᶜ)

open import Syntax.Grades.Traces.Allowance.AsOrder Op _≟ₒ_ cost cost-pos
  using (allowanceOrder)
open import Syntax.Grades.Traces.Allowance Op cost using (duration-≼ᵃ)

open import Syntax.Grades.Example.Traces.Lifted.TwoSided
  Op _≟ₒ_ cost coverageOrder allowanceOrder duration-≼ᶜ duration-≼ᵃ public
