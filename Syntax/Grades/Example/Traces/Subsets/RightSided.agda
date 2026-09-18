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
-- No list is greatest: no finite one permits every run. The carrier    --
-- therefore carries `any-run` as a point of its own, permitting any    --
-- run at all, possibly infinite, and absorbing. It is *not* the empty  --
-- list, which permits nothing and stays excluded.                      --
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

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades

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
-- The carrier: a written-out list of permitted runs, or any run at all

infix 50 permitting_

data Permits : Set₀ where
  permitting_ : NeTraces → Permits
  any-run     : Permits

permitting-inj : {P Q : NeTraces} → permitting P ≡ permitting Q → P ≡ Q
permitting-inj refl = refl

------------------------------------------------------------------------
-- The monoid: the language product, with `any-run` absorbing

infixl 7 _·ᵖ_

_·ᵖ_ : Permits → Permits → Permits
(permitting P) ·ᵖ (permitting Q) = permitting (P · Q)
(permitting _) ·ᵖ any-run        = any-run
any-run        ·ᵖ _              = any-run

uᵖ : Permits
uᵖ = permitting u

·ᵖ-identityʳ : (P : Permits) → P ·ᵖ uᵖ ≡ P
·ᵖ-identityʳ (permitting P) = cong permitting_ (·-identityʳ P)
·ᵖ-identityʳ any-run        = refl

·ᵖ-identityˡ : (P : Permits) → uᵖ ·ᵖ P ≡ P
·ᵖ-identityˡ (permitting P) = cong permitting_ (·-identityˡ P)
·ᵖ-identityˡ any-run        = refl

·ᵖ-assoc : (P Q R : Permits) → (P ·ᵖ Q) ·ᵖ R ≡ P ·ᵖ (Q ·ᵖ R)
·ᵖ-assoc (permitting P) (permitting Q) (permitting R) =
  cong permitting_ (·-assoc P Q R)
·ᵖ-assoc (permitting _) (permitting _) any-run        = refl
·ᵖ-assoc (permitting _) any-run        (permitting _) = refl
·ᵖ-assoc (permitting _) any-run        any-run        = refl
·ᵖ-assoc any-run        _              _              = refl

------------------------------------------------------------------------
-- The order: inclusion between lists, with `any-run` greatest

infix 5 _≾_

_≾_ : Permits → Permits → Set
(permitting P) ≾ (permitting Q) = P ≾₀ Q
(permitting _) ≾ any-run        = ⊤
any-run        ≾ (permitting _) = ⊥
any-run        ≾ any-run        = ⊤

≾-⊤ : (P : Permits) → P ≾ any-run
≾-⊤ (permitting _) = tt
≾-⊤ any-run        = tt

≾-refl : {P : Permits} → P ≾ P
≾-refl {permitting P} = ≾₀-refl {P}
≾-refl {any-run}      = tt

≾-trans : {P Q R : Permits} → P ≾ Q → Q ≾ R → P ≾ R
≾-trans {permitting P} {permitting Q} {permitting R} p q =
  ≾₀-trans {P} {Q} {R} p q
≾-trans {permitting _} {permitting _} {any-run}      p q = tt
≾-trans {permitting _} {any-run}      {permitting _} p ()
≾-trans {permitting _} {any-run}      {any-run}      p q = tt
≾-trans {any-run}      {permitting _} {_}            () q
≾-trans {any-run}      {any-run}      {permitting _} p ()
≾-trans {any-run}      {any-run}      {any-run}      p q = tt

≾-irrelevant : {P Q : Permits} → (p q : P ≾ Q) → p ≡ q
≾-irrelevant {permitting P} {permitting Q} p  q  = ≾₀-irrelevant {P} {Q} p q
≾-irrelevant {permitting _} {any-run}      tt tt = refl
≾-irrelevant {any-run}      {permitting _} () q
≾-irrelevant {any-run}      {any-run}      tt tt = refl

·-monoˡ : {C P Q : Permits} → P ≾ Q → (P ·ᵖ C) ≾ (Q ·ᵖ C)
·-monoˡ {permitting C} {permitting P} {permitting Q} p =
  ·-monoˡ₀ {C} {P} {Q} p
·-monoˡ {any-run}      {permitting _} {permitting _} p = tt
·-monoˡ {permitting _} {permitting _} {any-run}      p = tt
·-monoˡ {any-run}      {permitting _} {any-run}      p = tt
·-monoˡ {_}            {any-run}      {permitting _} ()
·-monoˡ {permitting _} {any-run}      {any-run}      p = tt
·-monoˡ {any-run}      {any-run}      {any-run}      p = tt

·-monoʳ : {C P Q : Permits} → P ≾ Q → (C ·ᵖ P) ≾ (C ·ᵖ Q)
·-monoʳ {permitting C} {permitting P} {permitting Q} p =
  ·-monoʳ₀ {C} {P} {Q} p
·-monoʳ {any-run}      {permitting _} {permitting _} p = tt
·-monoʳ {permitting _} {permitting _} {any-run}      p = tt
·-monoʳ {any-run}      {permitting _} {any-run}      p = tt
·-monoʳ {_}            {any-run}      {permitting _} ()
·-monoʳ {permitting _} {any-run}      {any-run}      p = tt
·-monoʳ {any-run}      {any-run}      {any-run}      p = tt

------------------------------------------------------------------------
-- Zero-product property
--
-- `any-run` is above the unit and not below it, so its clauses are
-- vacuous and the property is the sets' own.

≾-zero-productˡ : {P Q : Permits} → (P ·ᵖ Q) ≾ uᵖ → P ≾ uᵖ
≾-zero-productˡ {permitting P} {permitting Q} p = ≾₀-zero-productˡ {P} {Q} p
≾-zero-productˡ {permitting _} {any-run}      ()
≾-zero-productˡ {any-run}      {_}            ()

≾-zero-productʳ : {P Q : Permits} → (P ·ᵖ Q) ≾ uᵖ → Q ≾ uᵖ
≾-zero-productʳ {permitting P} {permitting Q} p = ≾₀-zero-productʳ {P} {Q} p
≾-zero-productʳ {permitting _} {any-run}      ()
≾-zero-productʳ {any-run}      {_}            ()

------------------------------------------------------------------------
-- Decidable equality, the inclusion of ℕ, and deciding the order

_≟ᴾ_ : DecidableEquality Permits
(permitting P) ≟ᴾ (permitting Q) with P ≟ᴺ Q
... | yes p = yes (cong permitting_ p)
... | no ¬p = no λ eq → ¬p (permitting-inj eq)
(permitting _) ≟ᴾ any-run        = no λ ()
any-run        ≟ᴾ (permitting _) = no λ ()
any-run        ≟ᴾ any-run        = yes refl

of-natᵖ : ℕ → Permits
of-natᵖ n = permitting (of-nat n)

of-natᵖ-zero : of-natᵖ 0 ≡ uᵖ
of-natᵖ-zero = cong permitting_ of-nat-zero

of-natᵖ-plus : {m n : ℕ} → of-natᵖ (m + n) ≡ of-natᵖ m ·ᵖ of-natᵖ n
of-natᵖ-plus {m} {n} = cong permitting_ (of-nat-plus {m} {n})

infix 5 _≾?_

_≾?_ : (P Q : Permits) → Dec (P ≾ Q)
(permitting P) ≾? (permitting Q) = P ≾₀? Q
(permitting _) ≾? any-run        = yes tt
any-run        ≾? (permitting _) = no λ ()
any-run        ≾? any-run        = yes tt

------------------------------------------------------------------------
-- The grade of sets of timed traces, read as upper bounds

right-sided : Grade
right-sided = record
  { Carrier         = Permits
  ; _·_             = _·ᵖ_
  ; u               = uᵖ
  ; ·-identityʳ     = ·ᵖ-identityʳ
  ; ·-identityˡ     = ·ᵖ-identityˡ
  ; ·-assoc         = ·ᵖ-assoc
  ; _≾_             = _≾_
  ; ⊤               = any-run
  ; ≾-⊤             = ≾-⊤
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; _≡?_            = _≟ᴾ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-nat          = of-natᵖ
  ; of-nat-zero     = of-natᵖ-zero
  ; of-nat-plus     = λ {m} {n} → of-natᵖ-plus {m} {n}
  }
