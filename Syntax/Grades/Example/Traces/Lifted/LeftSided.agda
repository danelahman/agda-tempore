------------------------------------------------------------------------
-- Antichains of timed traces as lower bounds.                        --
--                                                                    --
-- A grade is a non-empty finite set of traces, read as the           --
-- guarantees of a computation: writing `X` for the runs it may have, --
--                                                                    --
--   X is graded by P   iff   ∀ x ∈ X. ∃ p ∈ P. p ≼ x                 --
--                                                                    --
-- that is, in every run at least one of the listed traces is         --
-- covered. The quantifier is universal over the runs and existential --
-- over the set, so a longer list guarantees less, and the order that --
-- weakens the grade is                                               --
--                                                                    --
--   P ≾ P'   iff   ∀ p ∈ P. ∃ p' ∈ P'. p' ≼ p                        --
--                                                                    --
-- that is, every listed guarantee has a weaker one listed in `P'`.   --
-- Both endpoints are read disjunctively and weaken by gaining        --
-- members, and the union of two grades is their join. The            --
-- quantifiers range universally over the set of the *stronger* grade --
-- and existentially over that of the weaker, the mirror image of     --
-- `Lifted.RightSided`.                                               --
--                                                                    --
-- The order is `P ⊆ ↑P'`, so the closure is upward and the canonical --
-- form of a grade is the antichain of its `≼`-minimal members. The   --
-- carrier is the `Antichain` of `Traces.Reduced` at the order        --
-- itself, not at its converse, and the order is a partial order.     --
--                                                                    --
-- The fact specific to this module is that the unit `{ ε }` is the   --
-- greatest grade, the empty trace being covered by every run;        --
-- `TracePartialOrder` does not supply it.                            --
--                                                                    --
-- The construction does not otherwise inspect the order.             --
-- `Example.Traces.Timed.LeftSided` instantiates it at the coverage   --
-- order, in which only an operation covers a demand for that         --
-- operation.                                                         --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Minimum; Transitive; Trichotomous)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order
import Syntax.Grades.Traces.Reduced as Reduced

module Syntax.Grades.Example.Traces.Lifted.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (O : Order.TraceOrder Op) where

open import Data.List.Relation.Unary.Any using (here; any?)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (fromWitness)

open import Data.Maybe.Base using (nothing)

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

-- The unit is therefore not least: `of-nat 1` would be equal to it.

u⋠of-nat-1 : ¬ (u ≾ of-nat 1)
u⋠of-nat-1 rel with cong traces (≾-antisym {of-nat 1} {u} (≾-⊤ (of-nat 1)) rel)
... | ()

u-not-least : ¬ Minimum _≾_ u
u-not-least least = u⋠of-nat-1 (least (of-nat 1))

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
  ; u-least?        = nothing
  ; ·-comm?         = nothing
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
  ; _≾?_            = _≾?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
