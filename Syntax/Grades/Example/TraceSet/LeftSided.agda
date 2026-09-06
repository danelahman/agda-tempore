------------------------------------------------------------------------
-- Sets of timed traces, ordered up to the sub-trace preorder:         --
--                                                                     --
--   P ≾ Q   iff   every trace of P has some trace of Q inside it.     --
--                                                                     --
-- This is the Smyth upper lift of `Traces.Subtrace`'s preorder, and a  --
-- grade is read as a *lower* bound: `P` records what must have         --
-- happened, and a run realises `P` by doing at least what one of its   --
-- traces asks for. Weakening a grade therefore asks for less, exactly  --
-- as `[ m ,+∞⟩ ≾ [ n ,+∞⟩` weakens a left-sided interval by lowering   --
-- its bound.                                                           --
--                                                                     --
-- The direction matters for `unbox`, whose premise is `ρ' ≾ᵣ ρ` with   --
-- `ρ'` the effects that actually elapsed and `ρ` the box's grade. Read --
-- this way, a run that does *more* than `ρ` asks for still unboxes,    --
-- and one that does less never does.                                   --
--                                                                     --
-- The Hoare lower lift is the opposite reading -- a cap on what may     --
-- happen rather than a floor under what must -- and enters here only   --
-- as the second half of `TraceSet.Convex`.                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.TraceSet.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True)

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
-- `P ≾ Q` asks that every trace of `P` cover some trace of `Q`, which
-- is `_≽ˢ_` with the two sets the other way round. Unfolded, that is
-- `Sets.liftˢ` at the *converse* sub-trace preorder with `P` and `Q` in
-- the order written -- the same shape as `RightSided`'s order, which is
-- the lift at `_≼_` itself. At the level of the grades the two
-- one-sided orders therefore differ only in the direction of `_≼_`, and
-- not in which set the quantifier runs over.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces Q ≽ˢ traces P

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ≽ˢ-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} pq qr =
  ≽ˢ-trans {traces R} {traces Q} {traces P} qr pq

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces Q} {traces P} {traces C} {traces C} rel (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≽ˢ-·ˢ {traces C} {traces C} {traces Q} {traces P} (≽ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Zero-product property
--
-- The unit `{ ε }` asks for nothing, so every grade lies below it and
-- the zero-product property is vacuous -- as it is for the left-sided
-- intervals, whose unit `[ 0 ,+∞⟩` is likewise the greatest grade.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} _ = u-≽ˢ (traces P)

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} _ = u-≽ˢ (traces Q)

-- the grade order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable
--
-- Both the membership and the sub-trace preorder are decided and the
-- sets are finite, so an ordering between two written-out grades is
-- settled by computation.

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces Q ≽ˢ? traces P

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, ordered up to the
-- sub-trace preorder

left-sided-traces : Grade
left-sided-traces = record
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
