------------------------------------------------------------------------
-- Sets of timed traces as lower bounds, at the coverage order.        --
--                                                                    --
-- `Example.Traces.Lifted.LeftSided` at `Traces.Coverage`'s `_≼ᶜ_`: a  --
-- grade lists guarantees, and whatever the computation does, at least --
-- one of them has been covered -- every operation it names having     --
-- occurred, and every delay it names having been spent where it is    --
-- placed.                                                             --
--                                                                     --
-- A guarantee credits an operation with `costˡᵒ`, the least time it    --
-- can take.                                                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Example.Traces.Timed.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Coverage.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (coverageOrder)

open import Syntax.Grades.Example.Traces.Lifted.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans coverageOrder public
