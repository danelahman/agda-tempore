------------------------------------------------------------------------
-- The allowance partial order, packaged as a `TraceOrder`.           --
--                                                                    --
-- Everything the grade construction asks of an order on traces, in   --
-- one place: the comparison and its decision procedure, the          --
-- partial-order laws, monotonicity for the trace product, and the    --
-- two facts about the unit.                                          --
--                                                                    --
-- Positivity of `costʰⁱ` is a parameter: it is what makes the order  --
-- antisymmetric and the empty bound permit nothing but the empty     --
-- run, and so what the grades' zero-product law rests on.            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

open import Relation.Nullary using (¬_)

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Allowance.AsOrder
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costʰⁱ : Op → Duration.Carrier D)
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D)) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Order T Op
open import Grades.Traces.Allowance T Op costʰⁱ
open import Grades.Traces.Allowance.Antisym T Op costʰⁱ costʰⁱ-pos

open DecAllowance _≟ₒ_ using (_≼ᵃ?_)

allowancePartialOrder : TracePartialOrder
allowancePartialOrder = record
  { _≼_       = _≼ᵃ_
  ; _≼?_      = _≼ᵃ?_
  ; ≼-refl    = ≼ᵃ-refl
  ; ≼-trans   = λ p q → coe (+-identityʳ 0ᴰ) (≼ᵃ-trans p q)
  ; ≼-antisym = ≼ᵃ-antisym
  ; mono-∙    = mono-∙
  }

allowanceOrder : TraceOrder
allowanceOrder = record
  { base    = allowancePartialOrder
  ; ≼-nil   = nil
  ; ≼-ε-inv = ≼ᵃ-ε-inv costʰⁱ-pos
  }
