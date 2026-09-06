------------------------------------------------------------------------
-- Right-sided (capping) sets of timed traces, compared by the convex  --
-- (Egli-Milner) lift of a trace order `_≼_`:                          --
--                                                                     --
--   P ≾ Q   iff   every trace of P fits inside some trace of Q        --
--            and  every trace of Q has some trace of P inside it.     --
--                                                                     --
-- The mirror image of `Convex.LeftSided`: the same conjunction with    --
-- the two sets in the order they are written. The first conjunct is    --
-- `LowerLift.RightSided`'s order, the cap proper; the second is its    --
-- Smyth partner, which additionally stops the two sets drifting apart, --
-- so weakening may fill in between the listed allowances but not       --
-- extend past them.                                                   --
--                                                                     --
-- Unlike `Convex.LeftSided`, the unit says something here: a cap of    --
-- `{ ε }` permits only the instantaneous run, and both halves of the   --
-- order see that, which is what makes the zero-product property        --
-- non-vacuous in both of its conjuncts.                               --
--                                                                     --
-- The order lifted is a parameter: `Traces.Subtrace`'s lenient one and --
-- `Traces.SubtraceTimed`'s time-strict one both instantiate it, under  --
-- `Example.Traces.Subtrace` and `Example.Traces.SubtraceTimed`.        --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.Convex.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The convex order on (non-empty) sets of traces
--
-- Both halves compare the two sets in the order they are written, i.e.
-- with `P` on the left, as `LowerLift.RightSided` does.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = (traces P ≼ˢ traces Q) × (traces P ≽ˢ traces Q)

≾ᶜ-refl : {P : NeTraces} → P ≾ P
≾ᶜ-refl {P} = ≼ˢ-refl {traces P} , ≽ˢ-refl {traces P}

≾ᶜ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᶜ-trans {P} {Q} {R} (h₁ , s₁) (h₂ , s₂) =
    ≼ˢ-trans {traces P} {traces Q} {traces R} h₁ h₂
  , ≽ˢ-trans {traces P} {traces Q} {traces R} s₁ s₂

-- the language product is monotone in both arguments, half by half

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} (h , s) =
    ≼ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} h (≼ˢ-refl {traces C})
  , ≽ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} s (≽ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} (h , s) =
    ≼ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≼ˢ-refl {traces C}) h
  , ≽ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≽ˢ-refl {traces C}) s

------------------------------------------------------------------------
-- Zero-product property
--
-- A cap of `{ ε }` permits only the instantaneous run. The Hoare half
-- forces every trace of the product to take no time, and the Smyth half
-- forces one of them to; the trace monoid being conical, both descend
-- to each factor.

≾ᶜ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᶜ-zero-productˡ {P} {Q} (h , s) =
    ≼ˢ-zero-productˡ {traces P} {traces Q} (nonempty Q) h
  , ≽ˢ-zero-productˡ {traces P} {traces Q} (nonempty Q) s

≾ᶜ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᶜ-zero-productʳ {P} {Q} (h , s) =
    ≼ˢ-zero-productʳ {traces P} {traces Q} (nonempty P) h
  , ≽ˢ-zero-productʳ {traces P} {traces Q} (nonempty P) s

-- both halves are decided, so the order is proof-irrelevant

≾ᶜ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᶜ-irrelevant {P} {Q} (h , s) (h' , s') =
  cong₂ _,_ (liftˢ-irrelevant h h') (liftˢ-irrelevant s s')

------------------------------------------------------------------------
-- The order is decidable, half by half

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = (traces P ≼ˢ? traces Q) ×-dec (traces P ≽ˢ? traces Q)

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as a cap and
-- convexly ordered

convex-right-sided : Grade
convex-right-sided = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᶜ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᶜ-trans {i} {j} {k}
  ; _≡?_            = _≟ᴺ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᶜ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᶜ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᶜ-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
