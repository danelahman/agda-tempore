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
-- There is no greatest one: no finite list permits every run. So `⊤ᵍ`   --
-- is adjoined, permitting any run at all, possibly infinite, and       --
-- absorbing. It is *not* the empty list, which permits nothing and     --
-- stays excluded.                                                      --
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

open import Data.Unit using (tt)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades
open import Syntax.Grades.WithTop

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_

open WithDecEq _≟ₒ_
  using (_⊑_; _⊑?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; _≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The order on sets: inclusion, in the direction that permits more

infix 5 _≾₀_

_≾₀_ : NeTraces → NeTraces → Set
P ≾₀ Q = traces P ⊑ traces Q

≾₀-refl : {P : NeTraces} → P ≾₀ P
≾₀-refl {P} = ⊑-refl {traces P}

≾₀-trans : {P Q R : NeTraces} → P ≾₀ Q → Q ≾₀ R → P ≾₀ R
≾₀-trans {P} {Q} {R} = ⊑-trans {traces P} {traces Q} {traces R}

·-monoˡ₀ : {C P Q : NeTraces} → P ≾₀ Q → (P · C) ≾₀ (Q · C)
·-monoˡ₀ {C} rel = ⊑-·ˢ rel (⊑-refl {traces C})

·-monoʳ₀ : {C P Q : NeTraces} → P ≾₀ Q → (C · P) ≾₀ (C · Q)
·-monoʳ₀ {C} rel = ⊑-·ˢ (⊑-refl {traces C}) rel

-- a language product permitting nothing but the empty run has both
-- factors permitting nothing but it

≾₀-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾₀ u → P ≾₀ u
≾₀-zero-productˡ {P} {Q} = ⊑-zero-productˡ {traces P} {traces Q} (nonempty Q)

≾₀-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾₀ u → Q ≾₀ u
≾₀-zero-productʳ {P} {Q} = ⊑-zero-productʳ {traces P} {traces Q} (nonempty P)

≾₀-irrelevant : {P Q : NeTraces} → (p q : P ≾₀ Q) → p ≡ q
≾₀-irrelevant {P} {Q} = liftˢ-irrelevant

infix 5 _≾₀?_

_≾₀?_ : (P Q : NeTraces) → Dec (P ≾₀ Q)
P ≾₀? Q = traces P ⊑? traces Q

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
-- The grade of sets of timed traces, read as upper bounds, with `⊤ᵍ`
-- adjoined above them

open Adjoin base public
  renaming (Ext to Permits; _·ᵉ_ to _·ᵖ_; uᵉ to uᵖ; _≾ᵉ_ to _≾_;
            ≾ᵉ-⊤ to ≾-⊤; ≾ᵉ-refl to ≾-refl; ≾ᵉ-trans to ≾-trans;
            ≾ᵉ-irrelevant to ≾-irrelevant;
            ≾ᵉ-zero-productˡ to ≾-zero-productˡ;
            ≾ᵉ-zero-productʳ to ≾-zero-productʳ;
            ·ᵉ-monoˡ-≾ᵉ to ·-monoˡ; ·ᵉ-monoʳ-≾ᵉ to ·-monoʳ;
            _≡ᵉ?_ to _≟ᴾ_; withTop to right-sided)

infix 5 _≾?_

_≾?_ : (P Q : Permits) → Dec (P ≾ Q)
(only P) ≾? (only Q) = P ≾₀? Q
(only _) ≾? ⊤ᵍ       = yes tt
⊤ᵍ       ≾? (only _) = no λ ()
⊤ᵍ       ≾? ⊤ᵍ       = yes tt
