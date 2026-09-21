------------------------------------------------------------------------
-- Sets of timed traces as lower bounds.                               --
--                                                                     --
-- A grade is a non-empty finite set of traces, read as the guarantees --
-- a computation makes: writing `X` for the runs it may have,          --
--                                                                     --
--   X is graded by P   iff   ∀ x ∈ X. ∃ p ∈ P. p ≼ x                  --
--                                                                     --
-- -- whatever happens, at least one of the listed traces has been     --
-- covered. The quantifier is universal over the runs and existential  --
-- over the set, so a longer list guarantees less, and the order that  --
-- weakens the grade is                                                --
--                                                                     --
--   P ≾ P'   iff   ∀ p ∈ P. ∃ p' ∈ P'. p' ≼ p                         --
--                                                                     --
-- -- every listed guarantee has an easier one listed in `P'`. Both    --
-- endpoints are read disjunctively, both weaken by gaining members,   --
-- and the union of two grades is their join at either; note that the  --
-- quantifiers run universally over the *stronger* grade's set and     --
-- existentially over the weaker's, the mirror of `Lifted.RightSided`. --
--                                                                     --
-- Nothing here inspects the order. `Example.Traces.Timed.LeftSided`   --
-- instantiates it at the coverage order, the one a guarantee wants,   --
-- since there nothing but an operation covers a demand for it.        --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Relation.Nullary using (Dec)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ P' = traces P' ≽ˢ traces P

≾-refl : {P : NeTraces} → P ≾ P
≾-refl {P} = ≽ˢ-refl {traces P}

≾-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {P} {Q} {R} pq qr =
  ≽ˢ-trans {traces R} {traces Q} {traces P} qr pq

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces Q} {traces P} {traces C} {traces C} rel (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces C} {traces C} {traces Q} {traces P} (≽ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Binary joins
--
-- A grade is read disjunctively and weakens by gaining members, so the
-- union of two grades is their join, and the language product
-- distributes over it on both sides.

infixl 6 _⊔_

_⊔_ : NeTraces → NeTraces → NeTraces
_⊔_ = _∪_

⊔-ubˡ : (P Q : NeTraces) → P ≾ (P ⊔ Q)
⊔-ubˡ P Q = ≽ˢ-++-ubˡ {traces P} {traces Q}

⊔-ubʳ : (P Q : NeTraces) → Q ≾ (P ⊔ Q)
⊔-ubʳ P Q = ≽ˢ-++-ubʳ (traces P) {traces Q}

⊔-lub : {P Q R : NeTraces} → P ≾ R → Q ≾ R → (P ⊔ Q) ≾ R
⊔-lub {P} {Q} {R} = ≽ˢ-++-lub {traces P} {traces Q} {traces R}

·-distribˡ-⊔ : (C P Q : NeTraces) → (C · (P ⊔ Q)) ≾ ((C · P) ⊔ (C · Q))
·-distribˡ-⊔ C P Q = ≽ˢ-·ˢ-++ˡ {traces C} {traces P} {traces Q}

·-distribʳ-⊔ : (C P Q : NeTraces) → ((P ⊔ Q) · C) ≾ ((P · C) ⊔ (Q · C))
·-distribʳ-⊔ C P Q = ≽ˢ-·ˢ-++ʳ {traces P} {traces Q} {traces C}

------------------------------------------------------------------------
-- The greatest grade
--
-- The unit `{ ε }` guarantees nothing, the empty trace being covered by
-- every run, so it is already the greatest grade.

≾-⊤ : (P : NeTraces) → P ≾ u
≾-⊤ P = u-≽ˢ (traces P)

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit is greatest, so every grade lies below it and the property is
-- vacuous.

≾-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾-zero-productˡ {P} {Q} _ = u-≽ˢ (traces P)

≾-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾-zero-productʳ {P} {Q} _ = u-≽ˢ (traces Q)

-- the order is proof-irrelevant

≾-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces Q ≽ˢ? traces P

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as guarantees

left-sided : Grade
left-sided = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ⊤               = u
  ; ≾-⊤             = ≾-⊤
  ; _⊔_             = _⊔_
  ; ⊔-ubˡ           = ⊔-ubˡ
  ; ⊔-ubʳ           = ⊔-ubʳ
  ; ⊔-lub           = λ {P} {Q} {R} → ⊔-lub {P} {Q} {R}
  ; ·-distribˡ-⊔    = ·-distribˡ-⊔
  ; ·-distribʳ-⊔    = ·-distribʳ-⊔
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
