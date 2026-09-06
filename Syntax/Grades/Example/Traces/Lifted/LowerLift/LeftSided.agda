------------------------------------------------------------------------
-- Left-sided (flooring) sets of timed traces, compared up to a        --
-- trace order `_≼_`:                                                  --
--                                                                     --
--   P ≾ Q   iff   every trace of Q fits inside some trace of P.       --
--                                                                     --
-- `Inclusion.LeftSided` relaxed by `_≼_`: where that one asks each     --
-- required run of `Q` to be *literally* one of `P`'s, this one asks    --
-- only that it be covered by one of `P`'s. The two sets stay exchanged --
-- exactly as they are there, which is what makes the floor a floor --  --
-- a weaker grade requires less, and `P ≾ Q` says `P`'s demands         --
-- dominate `Q`'s.                                                     --
--                                                                     --
-- `LowerLift.RightSided` is the mirror image, the same comparison with --
-- the sets in the order they are written, and `Convex.LeftSided` is    --
-- this one strengthened by its Smyth partner.                         --
--                                                                     --
-- The order lifted is a parameter: `Traces.Subtrace`'s lenient one and --
-- `Traces.SubtraceTimed`'s time-strict one both instantiate it, under  --
-- `Example.Traces.Subtrace` and `Example.Traces.SubtraceTimed`.        --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.LowerLift.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Relation.Nullary using (Dec)

open import Syntax.Grades

-- the carrier and the monoid structure (`_·_`, `u`, `of-nat`, and their
-- laws), decidable equality `_≟ᴺ_`, and the irrelevance of the set-level
-- lift come from the shared set-of-traces module; only the order below
-- is specific to this grade

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces
--
-- `P ≾ Q` asks that every demand of `Q` be covered by some demand of
-- `P`, i.e. `_≼ˢ_` with the two sets exchanged.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces Q ≼ˢ traces P

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ≼ˢ-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} pq qr =
  ≼ˢ-trans {traces R} {traces Q} {traces P} qr pq

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces Q} {traces P} {traces C} {traces C} rel (≼ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces C} {traces C} {traces Q} {traces P} (≼ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit `{ ε }` demands nothing, and the empty trace fits inside
-- every trace, so every grade lies below it and the property is
-- vacuous -- as it is for the left-sided intervals, whose unit
-- `[ 0 ,+∞⟩` is likewise the greatest grade.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} _ = u-≼ˢ (traces P) (nonempty P)

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} _ = u-≼ˢ (traces Q) (nonempty Q)

-- the grade order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable
--
-- Both membership and the sub-trace preorder are decided and the sets
-- are finite, so an ordering between two written-out grades is settled
-- by computation.

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces Q ≼ˢ? traces P

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as a floor and
-- compared up to the sub-trace preorder

lower-lift-left-sided : Grade
lower-lift-left-sided = record
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
