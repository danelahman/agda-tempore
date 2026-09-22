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
--                                                                    --
-- Each order is taken at the cost model its side of the interval      --
-- wants: the floor credits an operation with `costˡᵒ`, the least time --
-- it can take, and the cap charges it `costʰⁱ`, the most. Only the    --
-- cap needs its costs positive, that being what makes an empty        --
-- allowance permit nothing but the empty run.                         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_; _<_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

module Syntax.Grades.Example.Traces.Timed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Syntax.Grades.Traces.Coverage.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ
  using (coverageOrder)
open import Syntax.Grades.Traces.Coverage Op costˡᵒ using (duration-≼ᶜ)

open import Syntax.Grades.Traces.Allowance.AsOrder
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costʰⁱ costʰⁱ-pos
  using (allowanceOrder)
open import Syntax.Grades.Traces.Allowance Op costʰⁱ using (duration-≼ᵃ)

open import Syntax.Grades.Example.Traces.Lifted.TwoSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans costˡᵒ costʰⁱ cost-≤
  coverageOrder allowanceOrder duration-≼ᶜ duration-≼ᵃ public
