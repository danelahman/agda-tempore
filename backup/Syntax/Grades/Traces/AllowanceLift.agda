------------------------------------------------------------------------
-- The set-level lifts of the allowance order.                         --
--                                                                    --
-- `Traces.OrderLift` at `Traces.Allowance`'s `_≼ᵃ_`, giving the Hoare --
-- lower lift and the Smyth upper lift of it, with their preorder      --
-- laws, monotonicity for the language product, how each sits against  --
-- the unit `{ ε }`, and the decision procedures.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _<_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Traces.AllowanceLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Syntax.Grades.Traces.Allowance.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (allowanceOrder)

open import Syntax.Grades.Traces.OrderLift
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans allowanceOrder public
