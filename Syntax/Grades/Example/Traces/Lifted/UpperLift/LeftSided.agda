------------------------------------------------------------------------
-- Left-sided (flooring) sets of timed traces, compared by the Smyth   --
-- upper lift of a trace order `_≼_`:                                  --
--                                                                     --
--   P ≾ Q   iff   every trace of P has some trace of Q inside it.     --
--                                                                     --
-- `UpperLift.RightSided` with the two sets exchanged, exactly as       --
-- `LowerLift.LeftSided` is `LowerLift.RightSided` exchanged. The grade --
-- is a *floor*: it lists what must have happened, and weakening asks   --
-- for less, so each demand on the left must be weakened by one on the  --
-- right.                                                              --
--                                                                     --
-- Reading a set of demands *disjunctively* -- a run discharges the     --
-- grade by covering any one of them -- is what this order is covariant --
-- for, which is what makes it, and not `LowerLift.LeftSided`, the      --
-- grade the "covers some member" Kripke frames are built over.         --
-- It is also `Convex.LeftSided`'s Smyth half.                          --
--                                                                     --
-- The order lifted is a parameter: `Traces.Subtrace`'s lenient one and --
-- `Traces.SubtraceTimed`'s time-strict one both instantiate it, under  --
-- `Example.Traces.Subtrace` and `Example.Traces.SubtraceTimed`.        --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.UpperLift.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Relation.Nullary using (Dec)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces
--
-- `P ≾ Q` asks that every demand of `P` be weakened by some demand of
-- `Q`, i.e. `_≽ˢ_` with the two sets exchanged.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces Q ≽ˢ traces P

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ≽ˢ-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} pq qr =
  ≽ˢ-trans {traces R} {traces Q} {traces P} qr pq

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces Q} {traces P} {traces C} {traces C} rel (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces C} {traces C} {traces Q} {traces P} (≽ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit `{ ε }` demands nothing, and the empty trace fits inside
-- every trace, so every grade lies below it and the property is
-- vacuous -- as it is for `LowerLift.LeftSided` and for the left-sided
-- time intervals, whose unit `[ 0 ,+∞⟩` is likewise the greatest grade.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} _ = u-≽ˢ (traces P)

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} _ = u-≽ˢ (traces Q)

-- the grade order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces Q ≽ˢ? traces P

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as a floor and
-- compared by the Smyth upper lift

upper-lift-left-sided : Grade
upper-lift-left-sided = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗ-trans {i} {j} {k}
  ; _≡?_            = _≟ᴺ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵗ-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
