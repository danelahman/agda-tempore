------------------------------------------------------------------------
-- Sets of timed traces as upper bounds.                               --
--                                                                     --
-- A grade is a non-empty finite set of traces, read as the bounds a    --
-- computation must stay within: writing `X` for the runs it may have,  --
--                                                                     --
--   X is graded by Q   iff   ∀ x ∈ X. ∃ q ∈ Q. x ≼ q                  --
--                                                                     --
-- -- every run stays within one of the listed bounds. The quantifier   --
-- is universal over the runs and existential over the set, so a longer --
-- list permits more, and the order that weakens the grade is the       --
-- Hoare (lower) lift of `_≼_` in the argument order written:           --
--                                                                     --
--   P ≾ Q   iff   ∀ p ∈ P. ∃ q ∈ Q. p ≼ q                             --
--                                                                     --
-- which is `↓P ⊆ ↓Q` for the sets of runs the two grades permit, and   --
-- makes the union of two grades their join.                            --
--                                                                     --
-- Nothing here inspects the order, so the construction is written once --
-- and instantiated -- `Example.Traces.Allowance` at the allowance      --
-- order. What the order decides is what "staying within a bound"       --
-- means, and there it means the bound's operations permit the run's    --
-- and its delays are a budget the run may spend where the bound places --
-- it.                                                                  --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Relation.Nullary using (Dec)

open import Syntax.Grades

-- the carrier and the monoid structure (`_·_`, `u`, `of-nat`, and their
-- laws), decidable equality `_≟ᴺ_`, and the irrelevance of the
-- set-level lift come from the shared set-of-traces module; only the
-- order below is specific to this grade

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces
--
-- `P ≾ Q` asks that every bound of `P` stay within some bound of `Q`,
-- which is `_≼ˢ_` in the order the two are written.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces P ≼ˢ traces Q

≾-refl : {P : NeTraces} → P ≾ P
≾-refl {P} = ≼ˢ-refl {traces P}

≾-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {P} {Q} {R} = ≼ˢ-trans {traces P} {traces Q} {traces R}

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} rel (≼ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≼ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit `{ ε }` permits nothing but the empty run, and durations add
-- along sequencing, so a product that stays within it has both factors
-- staying within it.

≾-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾-zero-productˡ {P} {Q} =
  ≼ˢ-zero-productˡ {traces P} {traces Q} (nonempty Q)

≾-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾-zero-productʳ {P} {Q} =
  ≼ˢ-zero-productʳ {traces P} {traces Q} (nonempty P)

-- the order is proof-irrelevant

≾-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable
--
-- Both membership and the underlying order are decided and the sets are
-- finite, so an ordering between two written-out grades is settled by
-- computation.

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces P ≼ˢ? traces Q

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as upper bounds

right-sided : Grade
right-sided = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; _≡?_            = _≟ᴺ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
