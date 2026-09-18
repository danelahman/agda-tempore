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
-- No list is then greatest: that would be the empty set of demands,    --
-- which is excluded. The carrier therefore carries `no-demand` as a    --
-- point of its own, above every list and absorbing -- once nothing is  --
-- demanded, sequencing demands nothing either.                         --
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

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades

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
-- The carrier: a written-out list of demanded runs, or no demand at all

infix 50 demanding_

data Demands : Set₀ where
  demanding_ : NeTraces → Demands
  no-demand  : Demands

demanding-inj : {P Q : NeTraces} → demanding P ≡ demanding Q → P ≡ Q
demanding-inj refl = refl

------------------------------------------------------------------------
-- The monoid: the language product, with `no-demand` absorbing

infixl 7 _·ᵈ_

_·ᵈ_ : Demands → Demands → Demands
(demanding P) ·ᵈ (demanding Q) = demanding (P · Q)
(demanding _) ·ᵈ no-demand     = no-demand
no-demand     ·ᵈ _             = no-demand

uᵈ : Demands
uᵈ = demanding u

·ᵈ-identityʳ : (P : Demands) → P ·ᵈ uᵈ ≡ P
·ᵈ-identityʳ (demanding P) = cong demanding_ (·-identityʳ P)
·ᵈ-identityʳ no-demand     = refl

·ᵈ-identityˡ : (P : Demands) → uᵈ ·ᵈ P ≡ P
·ᵈ-identityˡ (demanding P) = cong demanding_ (·-identityˡ P)
·ᵈ-identityˡ no-demand     = refl

·ᵈ-assoc : (P Q R : Demands) → (P ·ᵈ Q) ·ᵈ R ≡ P ·ᵈ (Q ·ᵈ R)
·ᵈ-assoc (demanding P) (demanding Q) (demanding R) =
  cong demanding_ (·-assoc P Q R)
·ᵈ-assoc (demanding _) (demanding _) no-demand     = refl
·ᵈ-assoc (demanding _) no-demand     (demanding _) = refl
·ᵈ-assoc (demanding _) no-demand     no-demand     = refl
·ᵈ-assoc no-demand     _             _             = refl

------------------------------------------------------------------------
-- The order: inclusion between lists, with `no-demand` greatest

infix 5 _≾_

_≾_ : Demands → Demands → Set
(demanding P) ≾ (demanding Q) = P ≾₀ Q
(demanding _) ≾ no-demand     = ⊤
no-demand     ≾ (demanding _) = ⊥
no-demand     ≾ no-demand     = ⊤

≾-⊤ : (P : Demands) → P ≾ no-demand
≾-⊤ (demanding _) = tt
≾-⊤ no-demand     = tt

≾-refl : {P : Demands} → P ≾ P
≾-refl {demanding P} = ≾₀-refl {P}
≾-refl {no-demand}   = tt

≾-trans : {P Q R : Demands} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {demanding P} {demanding Q} {demanding R} p q =
  ≾₀-trans {P} {Q} {R} p q
≾-trans {demanding _} {demanding _} {no-demand}   p q = tt
≾-trans {demanding _} {no-demand}   {demanding _} p ()
≾-trans {demanding _} {no-demand}   {no-demand}   p q = tt
≾-trans {no-demand}   {demanding _} {_}           () q
≾-trans {no-demand}   {no-demand}   {demanding _} p ()
≾-trans {no-demand}   {no-demand}   {no-demand}   p q = tt

≾-irrelevant : {P Q : Demands} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {demanding P} {demanding Q} p  q  = ≾₀-irrelevant {P} {Q} p q
≾-irrelevant {demanding _} {no-demand}   tt tt = refl
≾-irrelevant {no-demand}   {demanding _} () q
≾-irrelevant {no-demand}   {no-demand}   tt tt = refl

·-monoˡ : {C P Q : Demands} → P ≾ Q → (P ·ᵈ C) ≾ (Q ·ᵈ C)
·-monoˡ {demanding C} {demanding P} {demanding Q} p = ·-monoˡ₀ {C} {P} {Q} p
·-monoˡ {no-demand}   {demanding _} {demanding _} p = tt
·-monoˡ {demanding _} {demanding _} {no-demand}   p = tt
·-monoˡ {no-demand}   {demanding _} {no-demand}   p = tt
·-monoˡ {_}           {no-demand}   {demanding _} ()
·-monoˡ {demanding _} {no-demand}   {no-demand}   p = tt
·-monoˡ {no-demand}   {no-demand}   {no-demand}   p = tt

·-monoʳ : {C P Q : Demands} → P ≾ Q → (C ·ᵈ P) ≾ (C ·ᵈ Q)
·-monoʳ {demanding C} {demanding P} {demanding Q} p = ·-monoʳ₀ {C} {P} {Q} p
·-monoʳ {no-demand}   {demanding _} {demanding _} p = tt
·-monoʳ {demanding _} {demanding _} {no-demand}   p = tt
·-monoʳ {no-demand}   {demanding _} {no-demand}   p = tt
·-monoʳ {_}           {no-demand}   {demanding _} ()
·-monoʳ {demanding _} {no-demand}   {no-demand}   p = tt
·-monoʳ {no-demand}   {no-demand}   {no-demand}   p = tt

------------------------------------------------------------------------
-- Zero-product property
--
-- `no-demand` is above the unit and not below it, so its clauses are
-- vacuous and the property is the sets' own.

≾-zero-productˡ : {P Q : Demands} → (P ·ᵈ Q) ≾ uᵈ → P ≾ uᵈ
≾-zero-productˡ {demanding P} {demanding Q} p = ≾₀-zero-productˡ {P} {Q} p
≾-zero-productˡ {demanding _} {no-demand}   ()
≾-zero-productˡ {no-demand}   {_}           ()

≾-zero-productʳ : {P Q : Demands} → (P ·ᵈ Q) ≾ uᵈ → Q ≾ uᵈ
≾-zero-productʳ {demanding P} {demanding Q} p = ≾₀-zero-productʳ {P} {Q} p
≾-zero-productʳ {demanding _} {no-demand}   ()
≾-zero-productʳ {no-demand}   {_}           ()

------------------------------------------------------------------------
-- Decidable equality, the inclusion of ℕ, and deciding the order

_≟ᴰ_ : DecidableEquality Demands
(demanding P) ≟ᴰ (demanding Q) with P ≟ᴺ Q
... | yes p = yes (cong demanding_ p)
... | no ¬p = no λ eq → ¬p (demanding-inj eq)
(demanding _) ≟ᴰ no-demand     = no λ ()
no-demand     ≟ᴰ (demanding _) = no λ ()
no-demand     ≟ᴰ no-demand     = yes refl

of-natᵈ : ℕ → Demands
of-natᵈ n = demanding (of-nat n)

of-natᵈ-zero : of-natᵈ 0 ≡ uᵈ
of-natᵈ-zero = cong demanding_ of-nat-zero

of-natᵈ-plus : {m n : ℕ} → of-natᵈ (m + n) ≡ of-natᵈ m ·ᵈ of-natᵈ n
of-natᵈ-plus {m} {n} = cong demanding_ (of-nat-plus {m} {n})

infix 5 _≾?_

_≾?_ : (P Q : Demands) → Dec (P ≾ Q)
(demanding P) ≾? (demanding Q) = P ≾₀? Q
(demanding _) ≾? no-demand     = yes tt
no-demand     ≾? (demanding _) = no λ ()
no-demand     ≾? no-demand     = yes tt

------------------------------------------------------------------------
-- The grade of sets of timed traces, read as lower bounds

left-sided : Grade
left-sided = record
  { Carrier         = Demands
  ; _·_             = _·ᵈ_
  ; u               = uᵈ
  ; ·-identityʳ     = ·ᵈ-identityʳ
  ; ·-identityˡ     = ·ᵈ-identityˡ
  ; ·-assoc         = ·ᵈ-assoc
  ; _≾_             = _≾_
  ; ⊤               = no-demand
  ; ≾-⊤             = ≾-⊤
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; _≡?_            = _≟ᴰ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-nat          = of-natᵈ
  ; of-nat-zero     = of-natᵈ-zero
  ; of-nat-plus     = λ {m} {n} → of-natᵈ-plus {m} {n}
  }
