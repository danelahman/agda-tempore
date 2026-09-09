------------------------------------------------------------------------
-- Sets of timed traces as lower bounds, at the coverage order.        --
--                                                                    --
-- `Example.Traces.Lifted.LeftSided` at `Traces.Coverage`'s `_≼ᶜ_`: a  --
-- grade lists guarantees, and whatever the computation does, at least --
-- one of them has been covered -- every operation it names having     --
-- occurred, and every delay it names having been spent where it is    --
-- placed.                                                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Example.Traces.Coverage.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Coverage.AsOrder Op _≟ₒ_ cost
  using (coverageOrder)

open import Syntax.Grades.Example.Traces.Lifted.LeftSided
  Op _≟ₒ_ coverageOrder public
