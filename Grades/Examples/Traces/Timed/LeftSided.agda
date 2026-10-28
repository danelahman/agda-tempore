------------------------------------------------------------------------
-- Sets of timed traces as lower bounds, at the coverage order.       --
--                                                                    --
-- `Example.Traces.Lifted.LeftSided` at the order `_≼ᶜ_` of           --
-- `Traces.Coverage`: a grade lists guarantees, and in every run of   --
-- the computation at least one of them is covered, every operation   --
-- it lists having occurred and every delay it lists having elapsed   --
-- where it is placed.                                                --
--                                                                    --
-- A guarantee credits an operation with `costˡᵒ`, the least time it  --
-- can take.                                                          --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Examples.Traces.Timed.LeftSided
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → Duration.Carrier D) where

open import Grades.Traces.Coverage.AsOrder
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (coverageOrder)

open import Grades.Examples.Traces.Lifted.LeftSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans coverageOrder public
