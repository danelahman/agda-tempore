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
-- No finite list of bounds permits every run, so the carrier carries   --
-- `unbounded` as a point of its own: it permits any run at all,        --
-- however long, and is absorbing -- what follows an unbounded          --
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

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades

-- the sets of traces and their monoid structure (`_·_`, `u`, `of-nat`,
-- and their laws), decidable equality `_≟ᴺ_`, and the irrelevance of
-- the set-level lift come from the shared set-of-traces module; only
-- the order below is specific to this grade

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
-- The carrier: a written-out list of bounds, or no bound at all

infix 50 within_

data Bounds : Set₀ where
  within_   : NeTraces → Bounds
  unbounded : Bounds

within-inj : {P Q : NeTraces} → within P ≡ within Q → P ≡ Q
within-inj refl = refl

------------------------------------------------------------------------
-- The monoid: the language product, with `unbounded` absorbing

infixl 7 _·ᵇ_

_·ᵇ_ : Bounds → Bounds → Bounds
(within P) ·ᵇ (within Q) = within (P · Q)
(within _) ·ᵇ unbounded  = unbounded
unbounded  ·ᵇ _          = unbounded

uᵇ : Bounds
uᵇ = within u

·ᵇ-identityʳ : (P : Bounds) → P ·ᵇ uᵇ ≡ P
·ᵇ-identityʳ (within P) = cong within_ (·-identityʳ P)
·ᵇ-identityʳ unbounded  = refl

·ᵇ-identityˡ : (P : Bounds) → uᵇ ·ᵇ P ≡ P
·ᵇ-identityˡ (within P) = cong within_ (·-identityˡ P)
·ᵇ-identityˡ unbounded  = refl

·ᵇ-assoc : (P Q R : Bounds) → (P ·ᵇ Q) ·ᵇ R ≡ P ·ᵇ (Q ·ᵇ R)
·ᵇ-assoc (within P) (within Q) (within R) = cong within_ (·-assoc P Q R)
·ᵇ-assoc (within _) (within _) unbounded  = refl
·ᵇ-assoc (within _) unbounded  (within _) = refl
·ᵇ-assoc (within _) unbounded  unbounded  = refl
·ᵇ-assoc unbounded  _          _          = refl

------------------------------------------------------------------------
-- The order: the lift between lists, with `unbounded` greatest

infix 5 _≾_

_≾_ : Bounds → Bounds → Set
(within P) ≾ (within Q) = P ≾₀ Q
(within _) ≾ unbounded  = ⊤
unbounded  ≾ (within _) = ⊥
unbounded  ≾ unbounded  = ⊤

≾-⊤ : (P : Bounds) → P ≾ unbounded
≾-⊤ (within _) = tt
≾-⊤ unbounded  = tt

≾-refl : {P : Bounds} → P ≾ P
≾-refl {within P}  = ≾₀-refl {P}
≾-refl {unbounded} = tt

≾-trans : {P Q R : Bounds} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {within P}  {within Q}  {within R}  p q = ≾₀-trans {P} {Q} {R} p q
≾-trans {within _}  {within _}  {unbounded} p q = tt
≾-trans {within _}  {unbounded} {within _}  p ()
≾-trans {within _}  {unbounded} {unbounded} p q = tt
≾-trans {unbounded} {within _}  {_}         () q
≾-trans {unbounded} {unbounded} {within _}  p ()
≾-trans {unbounded} {unbounded} {unbounded} p q = tt

≾-irrelevant : {P Q : Bounds} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {within P}  {within Q}  p  q  = ≾₀-irrelevant {P} {Q} p q
≾-irrelevant {within _}  {unbounded} tt tt = refl
≾-irrelevant {unbounded} {within _}  () q
≾-irrelevant {unbounded} {unbounded} tt tt = refl

·-monoˡ : {C P Q : Bounds} → P ≾ Q → (P ·ᵇ C) ≾ (Q ·ᵇ C)
·-monoˡ {within C}  {within P}  {within Q}  p = ·-monoˡ₀ {C} {P} {Q} p
·-monoˡ {unbounded} {within _}  {within _}  p = tt
·-monoˡ {within _}  {within _}  {unbounded} p = tt
·-monoˡ {unbounded} {within _}  {unbounded} p = tt
·-monoˡ {_}         {unbounded} {within _}  ()
·-monoˡ {within _}  {unbounded} {unbounded} p = tt
·-monoˡ {unbounded} {unbounded} {unbounded} p = tt

·-monoʳ : {C P Q : Bounds} → P ≾ Q → (C ·ᵇ P) ≾ (C ·ᵇ Q)
·-monoʳ {within C}  {within P}  {within Q}  p = ·-monoʳ₀ {C} {P} {Q} p
·-monoʳ {unbounded} {within _}  {within _}  p = tt
·-monoʳ {within _}  {within _}  {unbounded} p = tt
·-monoʳ {unbounded} {within _}  {unbounded} p = tt
·-monoʳ {_}         {unbounded} {within _}  ()
·-monoʳ {within _}  {unbounded} {unbounded} p = tt
·-monoʳ {unbounded} {unbounded} {unbounded} p = tt

------------------------------------------------------------------------
-- Zero-product property
--
-- `unbounded` is above the unit and not below it, so its clauses are
-- vacuous and the property is the sets' own.

≾-zero-productˡ : {P Q : Bounds} → (P ·ᵇ Q) ≾ uᵇ → P ≾ uᵇ
≾-zero-productˡ {within P}  {within Q}  p = ≾₀-zero-productˡ {P} {Q} p
≾-zero-productˡ {within _}  {unbounded} ()
≾-zero-productˡ {unbounded} {_}         ()

≾-zero-productʳ : {P Q : Bounds} → (P ·ᵇ Q) ≾ uᵇ → Q ≾ uᵇ
≾-zero-productʳ {within P}  {within Q}  p = ≾₀-zero-productʳ {P} {Q} p
≾-zero-productʳ {within _}  {unbounded} ()
≾-zero-productʳ {unbounded} {_}         ()

------------------------------------------------------------------------
-- Decidable equality, the inclusion of ℕ, and deciding the order

_≟ᴮ_ : DecidableEquality Bounds
(within P) ≟ᴮ (within Q) with P ≟ᴺ Q
... | yes p = yes (cong within_ p)
... | no ¬p = no λ eq → ¬p (within-inj eq)
(within _) ≟ᴮ unbounded  = no λ ()
unbounded  ≟ᴮ (within _) = no λ ()
unbounded  ≟ᴮ unbounded  = yes refl

of-natᵇ : ℕ → Bounds
of-natᵇ n = within (of-nat n)

of-natᵇ-zero : of-natᵇ 0 ≡ uᵇ
of-natᵇ-zero = cong within_ of-nat-zero

of-natᵇ-plus : {m n : ℕ} → of-natᵇ (m + n) ≡ of-natᵇ m ·ᵇ of-natᵇ n
of-natᵇ-plus {m} {n} = cong within_ (of-nat-plus {m} {n})

infix 5 _≾?_

_≾?_ : (P Q : Bounds) → Dec (P ≾ Q)
(within P) ≾? (within Q) = P ≾₀? Q
(within _) ≾? unbounded  = yes tt
unbounded  ≾? (within _) = no λ ()
unbounded  ≾? unbounded  = yes tt

------------------------------------------------------------------------
-- The grade of sets of timed traces, read as upper bounds

right-sided : Grade
right-sided = record
  { Carrier         = Bounds
  ; _·_             = _·ᵇ_
  ; u               = uᵇ
  ; ·-identityʳ     = ·ᵇ-identityʳ
  ; ·-identityˡ     = ·ᵇ-identityˡ
  ; ·-assoc         = ·ᵇ-assoc
  ; _≾_             = _≾_
  ; ⊤               = unbounded
  ; ≾-⊤             = ≾-⊤
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; _≡?_            = _≟ᴮ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-nat          = of-natᵇ
  ; of-nat-zero     = of-natᵇ-zero
  ; of-nat-plus     = λ {m} {n} → of-natᵇ-plus {m} {n}
  }
