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
-- quantifiers range universally over the set of the stronger grade   --
-- and existentially over that of the weaker, the mirror image of     --
-- `Lifted.RightSided`.                                               --
--                                                                    --
-- The order is `P ⊆ ↑P'`, so the closure is upward and the canonical --
-- form of a grade is the antichain of its `≼`-minimal members. The   --
-- carrier is the `Antichain` of `Traces.Reduced` at the order        --
-- itself, not at its converse, and the order is a partial order.     --
--                                                                    --
-- The unit `{ ε }` is the greatest grade, the empty trace being      --
-- covered by every run. `TracePartialOrder` does not supply this,    --
-- and the construction does not otherwise inspect the order.         --
-- `Example.Traces.Timed.LeftSided` instantiates it at the coverage   --
-- order, in which only an operation covers a demand for that         --
-- operation.                                                         --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Minimum; Transitive; Trichotomous)

open import Util.Equality

import Grades.Traces.Order as Order
import Grades.Traces.Reduced as Reduced

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Examples.Traces.Lifted.LeftSided
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (O : Order.TraceOrder T Op) where

open import Data.List.Relation.Unary.Any using (here; any?)

open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)
open import Data.List.Properties using (∷-injectiveˡ)

open import Grades.Durations.Monus T using (Carrier; 0ᴰ; _<ᴰ_)
open import Relation.Nullary.Decidable using (fromWitness)

open import Grades.Base

open Order.TraceOrder O using (≼-nil)

-- the carrier and every law the order-theoretic half supplies: the
-- monoid, the order, its decision procedure, the joins and the
-- inclusion of durations

module R = Reduced T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans (Order.TraceOrder.base O)

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

≾-⊤ : (P : Antichain) → P ≾ 𝟏
≾-⊤ P s _ = fromWitness {a? = any? (_≽?_ s) (traces 𝟏)} (here ≼-nil)

-- The unit is therefore not least, once some duration is positive:
-- the delay by it would be equal to the unit.

𝟏⋠ι : (τ : Carrier) → 0ᴰ <ᴰ τ → ¬ (𝟏 ≾ ι τ)
𝟏⋠ι τ pos rel =
  delay≢ε (trans (sym (⟨⟩-pos τ pos))
                 (∷-injectiveˡ (cong traces (≾-antisym {ι τ} {𝟏} (≾-⊤ (ι τ)) rel))))
  where
    delay≢ε : ∀ {d} → delay d ε⁻ ≡ ε → ⊥
    delay≢ε ()

𝟏-not-least : (τ : Carrier) → 0ᴰ <ᴰ τ → ¬ Minimum _≾_ 𝟏
𝟏-not-least τ pos least = 𝟏⋠ι τ pos (least (ι τ))

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit is greatest, so every grade lies below it and the property is
-- vacuous.

≾-zero-productˡ : {P Q : Antichain} → (P · Q) ≾ 𝟏 → P ≾ 𝟏
≾-zero-productˡ {P} {Q} _ = ≾-⊤ P

≾-zero-productʳ : {P Q : Antichain} → (P · Q) ≾ 𝟏 → Q ≾ 𝟏
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

left-sided : Grade D
left-sided = posetᵍ record
  { Carrier         = Antichain
  ; _·_             = _·_
  ; 𝟏               = 𝟏
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ⊤               = 𝟏
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
  ; _≾?_            = _≾?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; ι               = ι
  ; ι-zero          = ι-zero
  ; ι-plus          = λ {m} {n} → ι-plus {m} {n}
  }
