------------------------------------------------------------------------
-- What a trace order has to supply to carry grades.                  --
--                                                                    --
-- The grades over timed traces differ only in which order they lift, --
-- the allowance order of `Traces.Allowance` or the coverage order of --
-- `Traces.Coverage`. The interface they meet comes in two layers.    --
--                                                                    --
-- `TracePartialOrder` is the order-theoretic half: decidability, the --
-- partial-order laws, and monotonicity for the trace product. It is  --
-- self-dual, so `flipᵖ` turns it into the converse, and that is why  --
-- it stands on its own: the antichain normal forms of                --
-- `Traces.Reduced` are taken with respect to it at both              --
-- handednesses, upward for the grades that close upward and downward --
-- for those that close downward.                                     --
--                                                                    --
-- `TraceOrder` adds the two facts about the unit that the grades'    --
-- zero-product properties rest on. Those are not self-dual (`ε ≼ t`  --
-- has no converse), so they make sense at one handedness only and    --
-- stay out of the layer that is flipped.                             --
--                                                                    --
-- Monotonicity is the demanding field: it fails for the prefix order --
-- (`Traces.Prefix`), and so contiguity-based orders carry no grade.  --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (Decidable)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Order {D : Duration} (T : TimeDomain D) (Op : Set) where

open import Grades.Traces.Base T Op

------------------------------------------------------------------------
-- The order-theoretic half

record TracePartialOrder : Set₁ where

  infix 4 _≼_

  field

    -- the comparison, and its decision procedure

    _≼_       : Trace → Trace → Set
    _≼?_      : Decidable _≼_

    -- a partial order

    ≼-refl    : (s : Trace) → s ≼ s
    ≼-trans   : {s t u : Trace} → s ≼ t → t ≼ u → s ≼ u
    ≼-antisym : {s t : Trace} → s ≼ t → t ≼ s → s ≡ t

    -- the trace product is monotone, in both arguments at once

    mono-∙    : {a a' b b' : Trace} → a ≼ a' → b ≼ b' → (a ∙ b) ≼ (a' ∙ b')

-- the converse, which meets the same interface

flipᵖ : TracePartialOrder → TracePartialOrder
flipᵖ P = record
  { _≼_       = λ s t → t ≼ s
  ; _≼?_      = λ s t → t ≼? s
  ; ≼-refl    = ≼-refl
  ; ≼-trans   = λ p q → ≼-trans q p
  ; ≼-antisym = λ p q → ≼-antisym q p
  ; mono-∙    = λ p q → mono-∙ p q
  }
  where open TracePartialOrder P

------------------------------------------------------------------------
-- The full interface
--
-- The order-theoretic half together with the two facts about the unit:
-- the empty demand is met by every run, and nothing but the empty
-- demand is met by a spent one.

record TraceOrder : Set₁ where

  field

    base : TracePartialOrder

  open TracePartialOrder base public

  field

    ≼-nil   : {t : Trace} → ε ≼ t
    ≼-ε-inv : {s : Trace} → s ≼ ε → s ≡ ε
