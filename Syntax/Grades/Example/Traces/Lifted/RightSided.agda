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
-- No finite list of bounds permits every run, so the grade has no      --
-- greatest element of its own and one is adjoined: `⊤ᵍ` permits any run --
-- at all, however long, and is absorbing -- what follows an unbounded  --
-- computation is unbounded too. It is *not* the empty set of bounds,   --
-- which permits nothing and is excluded.                               --
--                                                                     --
-- Nothing here inspects the order, so the construction is written once --
-- and instantiated -- `Example.Traces.Timed.RightSided` at the         --
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

open import Data.Unit using (tt)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades
open import Syntax.Grades.WithTop

-- the carrier and the monoid structure (`_·_`, `u`, `of-nat`, and their
-- laws), decidable equality `_≟ᴺ_`, and the irrelevance of the
-- set-level lift come from the shared set-of-traces module; only the
-- order below is specific to this grade

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The order on (non-empty) sets of traces
--
-- `P ≾₀ Q` asks that every bound of `P` stay within some bound of `Q`,
-- which is `_≼ˢ_` in the order the two are written.

infix 5 _≾₀_

_≾₀_ : NeTraces → NeTraces → Set
P ≾₀ Q = traces P ≼ˢ traces Q

≾₀-refl : {P : NeTraces} → P ≾₀ P
≾₀-refl {P} = ≼ˢ-refl {traces P}

≾₀-trans : {P Q R : NeTraces} → P ≾₀ Q → Q ≾₀ R → P ≾₀ R
≾₀-trans {P} {Q} {R} = ≼ˢ-trans {traces P} {traces Q} {traces R}

-- the language product is monotone in both arguments

·-monoˡ₀ : {C P Q : NeTraces} → P ≾₀ Q → (P · C) ≾₀ (Q · C)
·-monoˡ₀ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} rel (≼ˢ-refl {traces C})

·-monoʳ₀ : {C P Q : NeTraces} → P ≾₀ Q → (C · P) ≾₀ (C · Q)
·-monoʳ₀ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≼ˢ-refl {traces C}) rel

-- zero-product: the unit `{ ε }` permits nothing but the empty run, and
-- durations add along sequencing, so a product that stays within it has
-- both factors staying within it

≾₀-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾₀ u → P ≾₀ u
≾₀-zero-productˡ {P} {Q} =
  ≼ˢ-zero-productˡ {traces P} {traces Q} (nonempty Q)

≾₀-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾₀ u → Q ≾₀ u
≾₀-zero-productʳ {P} {Q} =
  ≼ˢ-zero-productʳ {traces P} {traces Q} (nonempty P)

-- the order is proof-irrelevant

≾₀-irrelevant : {P Q : NeTraces} → (p q : P ≾₀ Q) → p ≡ q
≾₀-irrelevant {P} {Q} = liftˢ-irrelevant

-- and decidable: both membership and the underlying order are decided
-- and the sets are finite, so an ordering between two written-out
-- grades is settled by computation

infix 5 _≾₀?_

_≾₀?_ : (P Q : NeTraces) → Dec (P ≾₀ Q)
P ≾₀? Q = traces P ≼ˢ? traces Q

------------------------------------------------------------------------
-- The sets of traces as an ordered monoid, before a top is adjoined

base : OrderedMonoid
base = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾₀_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ₀ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ₀ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾₀-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾₀-trans {i} {j} {k}
  ; _≡?_            = _≟ᴺ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾₀-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾₀-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾₀-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }

------------------------------------------------------------------------
-- The grade: those sets with `⊤ᵍ` adjoined above them

open Adjoin base public
  renaming (Ext to Bounds; _·ᵉ_ to _·ᵇ_; uᵉ to uᵇ; _≾ᵉ_ to _≾_;
            ≾ᵉ-⊤ to ≾-⊤; ≾ᵉ-refl to ≾-refl; ≾ᵉ-trans to ≾-trans;
            ≾ᵉ-irrelevant to ≾-irrelevant;
            ≾ᵉ-zero-productˡ to ≾-zero-productˡ;
            ≾ᵉ-zero-productʳ to ≾-zero-productʳ;
            ·ᵉ-monoˡ-≾ᵉ to ·-monoˡ; ·ᵉ-monoʳ-≾ᵉ to ·-monoʳ;
            _≡ᵉ?_ to _≟ᴮ_; withTop to right-sided)

-- the extended order is decided at the new point as well

infix 5 _≾?_

_≾?_ : (P Q : Bounds) → Dec (P ≾ Q)
(only P) ≾? (only Q) = P ≾₀? Q
(only _) ≾? ⊤ᵍ       = yes tt
⊤ᵍ       ≾? (only _) = no λ ()
⊤ᵍ       ≾? ⊤ᵍ       = yes tt
