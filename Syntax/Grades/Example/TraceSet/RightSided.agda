------------------------------------------------------------------------
-- (Right) one-sided sets of timed traces as grades:                   --
--                                                                     --
--   P ≾ Q   iff   every trace of P has some trace of Q above it.      --
--                                                                     --
-- The mirror image of `TraceSet.LeftSided`. A grade is read as a       --
-- *cap*: `P` records what a computation is permitted to have done,     --
-- and a run stays within it by doing at most what one of its traces    --
-- allows. Weakening a grade therefore permits more, exactly as         --
-- `[0, m ] ≾ [0, n ]` weakens a right-sided interval by raising its    --
-- bound.                                                               --
--                                                                     --
-- This is the Hoare lower lift of `Traces.Subtrace`'s preorder, where  --
-- the left-sided grade takes the Smyth upper one. Since `s ≼ t` reads  --
-- "the run `t` does at least what `s` asks for", the two lifts differ  --
-- only in which way the relation runs between the sets -- the trace    --
-- counterpart of `min i₂ ≤ min i₁` against `max i₁ ≤ max i₂`.          --
--                                                                     --
-- The unit `{ ε }` is the *least* grade here, permitting nothing but   --
-- an instantaneous run, just as `[0, 0 ]` is the least right-sided     --
-- interval. That is what makes the zero-product property say           --
-- something, unlike in the left-sided grade where it is vacuous.       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.TraceSet.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces
--
-- `P ≾ Q` asks that every trace of `P` be covered by some trace of `Q`,
-- which is `_≼ˢ_` with the sets in the order they are written -- that
-- is, `Sets.liftˢ` at `_≼_`. `LeftSided`'s order is the same lift at the
-- converse preorder, so the two differ only in the direction of `_≼_`.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces P ≼ˢ traces Q

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ≼ˢ-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} = ≼ˢ-trans {traces P} {traces Q} {traces R}

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
-- A cap of `{ ε }` permits only the instantaneous run, and the trace
-- monoid is conical, so a product capped at the unit has both factors
-- capped there.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} =
  ≼ˢ-zero-productˡ {traces P} {traces Q} (nonempty Q)

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} =
  ≼ˢ-zero-productʳ {traces P} {traces Q} (nonempty P)

-- the grade order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- The order is decidable

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces P ≼ˢ? traces Q

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as a cap

right-sided-traces : Grade
right-sided-traces = record
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
