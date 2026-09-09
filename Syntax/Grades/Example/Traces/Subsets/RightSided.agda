------------------------------------------------------------------------
-- Sets of timed traces as upper bounds, at the subset order.          --
--                                                                     --
-- A grade is a non-empty finite set of traces, read against the runs   --
-- `X` a computation may have as                                        --
--                                                                     --
--   X is graded by Q   iff   X ⊆ Q                                     --
--                                                                     --
-- -- at most the listed traces are exhibited. Nothing is approximated: --
-- a run either is one of the listed traces or it is not, so unlike     --
-- `Traces.Timed.RightSided` a listed delay buys nothing and a listed   --
-- operation permits nothing but itself.                                --
--                                                                     --
-- Weakening is therefore inclusion,                                    --
--                                                                     --
--   Q ≾ Q'   iff   Q ⊆ Q'                                              --
--                                                                     --
-- which is necessary (take `X := Q`) and sufficient (transitivity of   --
-- ⊆). The set is read *disjunctively*: a longer list permits more, the --
-- union of two grades is their join, and `{ ε }` -- permitting nothing --
-- but the empty run -- is the least grade.                             --
--                                                                     --
-- READINGS. As an *effect* grade this is a list of the runs a          --
-- computation may have, and `coerce` adds runs to that list. As a      --
-- *resource* grade it is a permit naming exactly the runs it covers,   --
-- and `unbox`'s `ρ' ≾ᵣ ρ` asks the elapsed runs to be among them.      --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Subsets.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Relation.Nullary using (Dec)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_

open WithDecEq _≟ₒ_
  using (_⊑_; _⊑?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; _≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order: inclusion, in the direction that permits more

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces P ⊑ traces Q

≾-refl : {P : NeTraces} → P ≾ P
≾-refl {P} = ⊑-refl {traces P}

≾-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {P} {Q} {R} = ⊑-trans {traces P} {traces Q} {traces R}

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} rel = ⊑-·ˢ rel (⊑-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} rel = ⊑-·ˢ (⊑-refl {traces C}) rel

-- a language product permitting nothing but the empty run has both
-- factors permitting nothing but it

≾-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾-zero-productˡ {P} {Q} = ⊑-zero-productˡ {traces P} {traces Q} (nonempty Q)

≾-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾-zero-productʳ {P} {Q} = ⊑-zero-productʳ {traces P} {traces Q} (nonempty P)

≾-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {P} {Q} = liftˢ-irrelevant

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces P ⊑? traces Q

------------------------------------------------------------------------
-- The grade of sets of timed traces, read as upper bounds

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
