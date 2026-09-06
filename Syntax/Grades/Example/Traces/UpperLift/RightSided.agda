------------------------------------------------------------------------
-- Right-sided (capping) sets of timed traces, compared by the Smyth   --
-- upper lift of the sub-trace preorder:                               --
--                                                                     --
--   P ≾ Q   iff   every trace of Q has some trace of P inside it.     --
--                                                                     --
-- The mirror of `LowerLift.RightSided`: the same two sets in the same  --
-- order, but with the quantifier running over the *right-hand* set     --
-- rather than the left. Where the Hoare lift asks each trace on the    --
-- left to be covered somewhere on the right, this one asks each trace  --
-- on the right to be justified by something on the left -- the "must"  --
-- reading against the Hoare lift's "may".                             --
--                                                                     --
-- `UpperLift.LeftSided` is this comparison with the sets exchanged,    --
-- and `Convex.RightSided` is the two of them conjoined.               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.UpperLift.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Relation.Nullary using (Dec)

open import Syntax.Grades

-- the carrier and the monoid structure (`_·_`, `u`, `of-nat`, and their
-- laws), decidable equality `_≟ᴺ_`, and the irrelevance of the set-level
-- lift come from the shared set-of-traces module; only the order below
-- is specific to this grade

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces
--
-- `P ≾ Q` asks that every allowance of `Q` be realised by something `P`
-- already offers, i.e. `_≽ˢ_` with the sets in the order written.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces P ≽ˢ traces Q

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ≽ˢ-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} = ≽ˢ-trans {traces P} {traces Q} {traces R}

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} rel (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≽ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Zero-product property
--
-- A cap of `{ ε }` asks for one member below the empty trace, which the
-- trace monoid being conical forces to be `ε` itself; one factor of a
-- language product supplies it, so the property descends to both.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} =
  ≽ˢ-zero-productˡ {traces P} {traces Q} (nonempty Q)

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} =
  ≽ˢ-zero-productʳ {traces P} {traces Q} (nonempty P)

-- the grade order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces P ≽ˢ? traces Q

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as a cap and
-- compared by the Smyth upper lift

upper-lift-right-sided : Grade
upper-lift-right-sided = record
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
