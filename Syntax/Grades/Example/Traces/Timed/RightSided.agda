------------------------------------------------------------------------
-- Sets of timed traces as upper bounds, at the allowance order.      --
--                                                                    --
-- `Example.Traces.Lifted.RightSided` at the order `_≼ᵃ_` of          --
-- `Traces.Allowance`. A grade lists bounds, and a run stays within a --
-- bound when the bound lists every operation the run performs, or    --
-- leaves enough budget to cover those it does not list, and enough   --
-- for the idling of the run. The budget is local: what the bound     --
-- offers between two listed operations pays only for what the run    --
-- does between the same two.                                         --
--                                                                    --
-- A bound charges an operation `costʰⁱ`, the most time it can take.  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Example.Traces.Timed.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Syntax.Grades.Traces.Allowance.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (allowanceOrder)

open import Syntax.Grades.Example.Traces.Lifted.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans allowanceOrder public
