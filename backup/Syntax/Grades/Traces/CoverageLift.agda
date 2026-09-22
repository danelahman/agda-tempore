------------------------------------------------------------------------
-- The set-level lifts of the coverage order.                          --
--                                                                    --
-- `Traces.OrderLift` at `Traces.Coverage`'s `_≼ᶜ_`, giving the Hoare  --
-- lower lift and the Smyth upper lift of it, with their preorder      --
-- laws, monotonicity for the language product, how each sits against  --
-- the unit `{ ε }`, and the decision procedures.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Traces.CoverageLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Coverage.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (coverageOrder)

open import Syntax.Grades.Traces.OrderLift
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans coverageOrder public
