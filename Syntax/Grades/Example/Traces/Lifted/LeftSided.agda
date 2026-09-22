------------------------------------------------------------------------
-- Antichains of timed traces as lower bounds.                         --
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
-- That reading is `P ⊆ ↑P'`, so the closure is upward and the         --
-- canonical form of a grade is the antichain of its `≼`-minimal       --
-- members. The carrier is therefore `Traces.Reduced`'s `Antichain` at --
-- the order as given -- not at its converse -- and the order is a     --
-- partial one: mutually-weakening grades are equal.                   --
--                                                                     --
-- What is proper to this module is the unit `{ ε }`: it is the        --
-- greatest grade, the empty trace being covered by every run, and     --
-- that is the one fact the reduction's `TracePartialOrder` cannot     --
-- supply.                                                             --
--                                                                     --
-- Nothing here inspects the order otherwise.                          --
-- `Example.Traces.Timed.LeftSided` instantiates it at the coverage    --
-- order, the one a guarantee wants, since there nothing but an        --
-- operation covers a demand for it.                                   --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order
import Syntax.Grades.Traces.Reduced as Reduced

module Syntax.Grades.Example.Traces.Lifted.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (O : Order.TraceOrder Op) where

open import Data.List.Relation.Unary.Any using (here; any?)

open import Relation.Nullary.Decidable using (fromWitness)

open import Syntax.Grades

open Order.TraceOrder O using (≼-nil)

-- the carrier and every law the order-theoretic half supplies: the
-- monoid, the order, its decision procedure, the joins and the
-- inclusion of the naturals

module R = Reduced Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans (Order.TraceOrder.base O)

open R public hiding (≾-antisym)

------------------------------------------------------------------------
-- Antisymmetry
--
-- Mutually-weakening grades are propositionally equal, an antichain
-- being determined by the closure the order reads.

≾-antisym : {P Q : Antichain} → P ≾ Q → Q ≾ P → P ≡ Q
≾-antisym = R.≾-antisym

------------------------------------------------------------------------
-- The greatest grade
--
-- The unit `{ ε }` guarantees nothing, the empty trace being covered by
-- every run, so it is already the greatest grade.

≾-⊤ : (P : Antichain) → P ≾ u
≾-⊤ P s _ = fromWitness {a? = any? (_≽?_ s) (traces u)} (here ≼-nil)

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit is greatest, so every grade lies below it and the property is
-- vacuous.

≾-zero-productˡ : {P Q : Antichain} → (P · Q) ≾ u → P ≾ u
≾-zero-productˡ {P} {Q} _ = ≾-⊤ P

≾-zero-productʳ : {P Q : Antichain} → (P · Q) ≾ u → Q ≾ u
≾-zero-productʳ {P} {Q} _ = ≾-⊤ Q

------------------------------------------------------------------------
-- Distributivity, read at the order
--
-- The two sides are equal antichains, so the grade's one-directional
-- law is that equation transported.

·-distribˡ-⊔-≾ : (C P Q : Antichain) → (C · (P ⊔ Q)) ≾ ((C · P) ⊔ (C · Q))
·-distribˡ-⊔-≾ C P Q =
  subst ((C · (P ⊔ Q)) ≾_) (·-distribˡ-⊔ C P Q) (≾-refl {C · (P ⊔ Q)})

·-distribʳ-⊔-≾ : (C P Q : Antichain) → ((P ⊔ Q) · C) ≾ ((P · C) ⊔ (Q · C))
·-distribʳ-⊔-≾ C P Q =
  subst (((P ⊔ Q) · C) ≾_) (·-distribʳ-⊔ C P Q) (≾-refl {(P ⊔ Q) · C})

------------------------------------------------------------------------
-- The grade of antichains of timed traces, read as guarantees

left-sided : Grade
left-sided = record
  { Carrier         = Antichain
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
  ; ·-distribˡ-⊔-≾  = ·-distribˡ-⊔-≾
  ; ·-distribʳ-⊔-≾  = ·-distribʳ-⊔-≾
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; ≾-antisym       = λ {P} {Q} → ≾-antisym {P} {Q}
  ; _≡?_            = _≟ᴬ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
