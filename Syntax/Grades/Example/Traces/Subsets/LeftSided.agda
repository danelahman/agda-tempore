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
-- and a longer list demands more.                                      --
--                                                                     --
-- There is then no greatest set: that would be the empty set of        --
-- demands, which is excluded. So `⊤ᵍ` is adjoined, demanding nothing   --
-- at all, and it is absorbing -- once nothing is demanded, sequencing  --
-- demands nothing either. (Absorption is forced: `⊤ᵍ · C` has to be    --
-- above every `P · C`, and the only set included in all of them is the --
-- empty one.)                                                          --
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
open import Data.Unit using (tt)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades
open import Syntax.Grades.WithTop

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_

open WithDecEq _≟ₒ_
  using (_⊑_; _⊑?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; _≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The order on sets: inclusion, in the direction that demands less

infix 5 _≾₀_

_≾₀_ : NeTraces → NeTraces → Set
P ≾₀ P' = traces P' ⊑ traces P

≾₀-refl : {P : NeTraces} → P ≾₀ P
≾₀-refl {P} = ⊑-refl {traces P}

≾₀-trans : {P Q R : NeTraces} → P ≾₀ Q → Q ≾₀ R → P ≾₀ R
≾₀-trans {P} {Q} {R} pq qr = ⊑-trans {traces R} {traces Q} {traces P} qr pq

·-monoˡ₀ : {C P Q : NeTraces} → P ≾₀ Q → (P · C) ≾₀ (Q · C)
·-monoˡ₀ {C} rel = ⊑-·ˢ rel (⊑-refl {traces C})

·-monoʳ₀ : {C P Q : NeTraces} → P ≾₀ Q → (C · P) ≾₀ (C · Q)
·-monoʳ₀ {C} rel = ⊑-·ˢ (⊑-refl {traces C}) rel

-- a language product all of whose demands stopping meets has both
-- factors demanding only that: the empty run decomposes only as itself

≾₀-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾₀ u → P ≾₀ u
≾₀-zero-productˡ {P} {Q} rel =
  u-⊑ (proj₁ (ε∈-·ˢ⁻ {traces P} {traces Q} (⊑-u rel)))

≾₀-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾₀ u → Q ≾₀ u
≾₀-zero-productʳ {P} {Q} rel =
  u-⊑ (proj₂ (ε∈-·ˢ⁻ {traces P} {traces Q} (⊑-u rel)))

≾₀-irrelevant : {P Q : NeTraces} → (p q : P ≾₀ Q) → p ≡ q
≾₀-irrelevant {P} {Q} = liftˢ-irrelevant

infix 5 _≾₀?_

_≾₀?_ : (P Q : NeTraces) → Dec (P ≾₀ Q)
P ≾₀? Q = traces Q ⊑? traces P

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
-- The grade of sets of timed traces, read as lower bounds, with `⊤ᵍ`
-- adjoined above them

open Adjoin base public
  renaming (Ext to Demands; _·ᵉ_ to _·ᵈ_; uᵉ to uᵈ; _≾ᵉ_ to _≾_;
            ≾ᵉ-⊤ to ≾-⊤; ≾ᵉ-refl to ≾-refl; ≾ᵉ-trans to ≾-trans;
            ≾ᵉ-irrelevant to ≾-irrelevant;
            ≾ᵉ-zero-productˡ to ≾-zero-productˡ;
            ≾ᵉ-zero-productʳ to ≾-zero-productʳ;
            ·ᵉ-monoˡ-≾ᵉ to ·-monoˡ; ·ᵉ-monoʳ-≾ᵉ to ·-monoʳ;
            _≡ᵉ?_ to _≟ᴰ_; withTop to left-sided)

infix 5 _≾?_

_≾?_ : (P Q : Demands) → Dec (P ≾ Q)
(only P) ≾? (only Q) = P ≾₀? Q
(only _) ≾? ⊤ᵍ       = yes tt
⊤ᵍ       ≾? (only _) = no λ ()
⊤ᵍ       ≾? ⊤ᵍ       = yes tt
