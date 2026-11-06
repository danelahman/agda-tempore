------------------------------------------------------------------------
-- Banked trace upper bounds: sets of timed traces at the allowance   --
-- order.                                                             --
--                                                                    --
-- `Traces.Lifted.UpperBound` at the order `_≼ᵃ_` of                  --
-- `Traces.Allowance`. A grade lists bounds, and a run stays within a --
-- bound when the bound lists every operation the run performs, or    --
-- leaves enough budget to cover those it does not list, and enough   --
-- for the idling of the run. The budget is local: what the bound     --
-- offers between two listed operations pays only for what the run    --
-- does between the same two.                                         --
--                                                                    --
-- A bound charges an operation `costʰⁱ`, the most time it can take.  --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Relation.Nullary using (¬_)

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Examples.Traces.Banked.UpperBound
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → Duration.Carrier D)
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D)) where

open import Grades.Traces.Allowance.AsOrder
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (allowanceOrder)

open import Grades.Examples.Traces.Lifted.UpperBound
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans allowanceOrder public
