------------------------------------------------------------------------
-- What a trace order has to supply to carry grades.                   --
--                                                                     --
-- Several preorders on timed traces are in play -- the allowance order --
-- of `Traces.Allowance`, and the sub-trace orders parked under         --
-- `backup/` -- and the grades built over them differ only in which one --
-- they lift. This record is the interface they meet:                   --
-- decidability, the preorder laws, monotonicity for the trace product, --
-- and the two facts about the unit that the zero-product properties    --
-- rest on.                                                            --
--                                                                     --
-- Monotonicity is the demanding field. It is what fails for the prefix --
-- order (`Traces.Prefix`), and it is why contiguity-based orders carry --
-- no grade at all.                                                    --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (Decidable)

open import Util.Equality

module Syntax.Grades.Traces.Order (Op : Set) where

open import Syntax.Grades.Traces.Base Op

record TraceOrder : Set₁ where

  infix 4 _≼_

  field

    -- the comparison, and its decision procedure

    _≼_     : Trace → Trace → Set
    _≼?_    : Decidable _≼_

    -- a preorder

    ≼-refl  : (s : Trace) → s ≼ s
    ≼-trans : {s t u : Trace} → s ≼ t → t ≼ u → s ≼ u

    -- the empty demand is met by every run

    ≼-nil   : {t : Trace} → ε ≼ t

    -- the trace product is monotone, in both arguments at once

    mono-∙  : {a a' b b' : Trace} → a ≼ a' → b ≼ b' → (a ∙ b) ≼ (a' ∙ b')

    -- and nothing but the empty demand is met by a spent run

    ≼-ε-inv : {s : Trace} → s ≼ ε → s ≡ ε
