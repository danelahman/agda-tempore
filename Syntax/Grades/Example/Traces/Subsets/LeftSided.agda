------------------------------------------------------------------------
-- Sets of timed traces as lower bounds, at the subset order.          --
--                                                                     --
-- A grade is a non-empty finite set of traces, read against the runs   --
-- `X` a computation may have as                                        --
--                                                                     --
--   X is graded by P   iff   P ⊆ X                                     --
--                                                                     --
-- -- each listed trace is a run the computation can exhibit. This is   --
-- the only lower bound the subset order admits. The reading "whatever  --
-- happened, it was one of the listed traces" is `X ⊆ P`, which is the  --
-- *cap*'s condition, equality leaving nothing for the two endpoints to --
-- differ about; the ordered families keep them apart by what their     --
-- comparison lets one trace do for another, and there is none here.    --
--                                                                     --
-- Weakening drops listed traces,                                       --
--                                                                     --
--   P ≾ P'   iff   P' ⊆ P                                              --
--                                                                     --
-- necessary (take `X := P`) and sufficient (transitivity of ⊆). So the --
-- set is read *conjunctively* -- every member is a separate demand --   --
-- and a longer list demands more. `{ ε }` is the greatest grade,       --
-- demanding only that stopping is possible.                            --
--                                                                     --
-- READINGS. As an *effect* grade this is a reachability claim about a  --
-- computation's branches, and `coerce` forgets branches; a non-        --
-- singleton grade needs a branching construct whose rule takes the     --
-- union of its branches' grades, since coercing both branches to one   --
-- grade would have to intersect them. As a *resource* grade it is a    --
-- demand that every listed run be available, which `unbox`'s           --
-- `ρ' ≾ᵣ ρ` discharges by having what elapsed cover all of them.       --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Subsets.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (Dec)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_

open WithDecEq _≟ₒ_
  using (_⊑_; _⊑?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; _≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The grade order: inclusion, in the direction that demands less

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ P' = traces P' ⊑ traces P

≾-refl : {P : NeTraces} → P ≾ P
≾-refl {P} = ⊑-refl {traces P}

≾-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {P} {Q} {R} pq qr = ⊑-trans {traces R} {traces Q} {traces P} qr pq

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} rel = ⊑-·ˢ rel (⊑-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} rel = ⊑-·ˢ (⊑-refl {traces C}) rel

-- a language product all of whose demands stopping meets has both
-- factors demanding only that: the empty run decomposes only as itself

≾-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾-zero-productˡ {P} {Q} rel =
  u-⊑ (proj₁ (ε∈-·ˢ⁻ {traces P} {traces Q} (⊑-u rel)))

≾-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾-zero-productʳ {P} {Q} rel =
  u-⊑ (proj₂ (ε∈-·ˢ⁻ {traces P} {traces Q} (⊑-u rel)))

≾-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {P} {Q} = liftˢ-irrelevant

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces Q ⊑? traces P

------------------------------------------------------------------------
-- The grade of sets of timed traces, read as lower bounds

left-sided : Grade
left-sided = record
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
