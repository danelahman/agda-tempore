------------------------------------------------------------------------
-- Sets of timed traces as upper bounds, at the subset order.         --
--                                                                    --
-- A grade is a non-empty finite set of traces, read against the runs --
-- `X` a computation may have as                                      --
--                                                                    --
--   X is graded by Q   iff   X ⊆ Q                                   --
--                                                                    --
-- that is, the computation exhibits only listed traces. A run is one --
-- of the listed traces or it is not: unlike under                    --
-- `Traces.Timed.RightSided`, a listed delay pays for nothing and a   --
-- listed operation permits only itself.                              --
--                                                                    --
-- Weakening is inclusion,                                            --
--                                                                    --
--   Q ≾ Q'   iff   Q ⊆ Q'                                            --
--                                                                    --
-- and the set is read *disjunctively*: a longer list permits more,   --
-- and the union of two grades is their join. There is no least       --
-- grade: `{ ε }`, permitting only the empty run, lies below only the --
-- lists that contain the empty run.                                  --
--                                                                    --
-- No finite list permits every run, and the carrier has `any-run` as --
-- a separate point, permitting any run, possibly infinite, and       --
-- absorbing. It is distinct from the empty list, which permits       --
-- nothing and is excluded.                                           --
--                                                                    --
-- As an *effect* grade this is a list of the runs a computation may  --
-- have, and `coerce` adds runs to it. As a *resource* grade it is a  --
-- permit listing exactly the runs it covers, and the premise         --
-- `ρ' ≾ᵣ ρ` of `unbox` requires the elapsed runs to be among them.   --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Minimum; Transitive; Trichotomous)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)

module Syntax.Grades.Example.Traces.Subsets.RightSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_) where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)

open import Data.Maybe.Base using (nothing)

open import Syntax.Durations.Nat using (ℕᴰ)
open import Syntax.Grades

open import Syntax.Grades.Traces.Sets ℕᵀ Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans

open WithDecEq _≟ₒ_
  using (_⊑_; _⊑?_; ⊑-refl; ⊑-trans; ⊑-·; liftˢ-irrelevant;
         _≟ᵀ_; ⊑-∪-ubˡ; ⊑-∪-ubʳ; ⊑-∪-lub; ⊑-nfˡ⁻; ⊑-antisym)

------------------------------------------------------------------------
-- The order on sets: inclusion, in the direction that permits more

infix 5 _≾₀_

_≾₀_ : NeTraces → NeTraces → Set
P ≾₀ Q = traces P ⊑ traces Q

≾₀-refl : {P : NeTraces} → P ≾₀ P
≾₀-refl {P} = ⊑-refl {traces P}

≾₀-trans : {P Q R : NeTraces} → P ≾₀ Q → Q ≾₀ R → P ≾₀ R
≾₀-trans {P} {Q} {R} = ⊑-trans {traces P} {traces Q} {traces R}

-- mutual inclusion is equality of the permitted runs, and a set is the
-- canonical list of its members, so the order is antisymmetric

≾₀-antisym : {P Q : NeTraces} → P ≾₀ Q → Q ≾₀ P → P ≡ Q
≾₀-antisym {P} {Q} p q = ne-ext (⊑-antisym (sorted P) (sorted Q) p q)

·-monoˡ₀ : {C P Q : NeTraces} → P ≾₀ Q → (P · C) ≾₀ (Q · C)
·-monoˡ₀ {C} rel = ⊑-· rel (⊑-refl {traces C})

·-monoʳ₀ : {C P Q : NeTraces} → P ≾₀ Q → (C · P) ≾₀ (C · Q)
·-monoʳ₀ {C} rel = ⊑-· (⊑-refl {traces C}) rel

-- the permitted runs are listed disjunctively, so the union of two
-- sets is their join, and the language product distributes over it on
-- both sides

⊔₀-ubˡ : (P Q : NeTraces) → P ≾₀ (P ∪ Q)
⊔₀-ubˡ P Q = ⊑-∪-ubˡ {traces P} {traces Q}

⊔₀-ubʳ : (P Q : NeTraces) → Q ≾₀ (P ∪ Q)
⊔₀-ubʳ P Q = ⊑-∪-ubʳ (traces P) {traces Q}

⊔₀-lub : {P Q R : NeTraces} → P ≾₀ R → Q ≾₀ R → (P ∪ Q) ≾₀ R
⊔₀-lub {P} {Q} {R} = ⊑-∪-lub {traces P} {traces Q} {traces R}

-- distributivity holds on the nose: the two sides list the same runs,
-- and a set is determined by the runs it lists

·-distribˡ₀-⊔ : (C P Q : NeTraces) → (C · (P ∪ Q)) ≾₀ ((C · P) ∪ (C · Q))
·-distribˡ₀-⊔ C P Q =
  subst ((C · (P ∪ Q)) ≾₀_) (·-distribˡ-∪ C P Q) (≾₀-refl {C · (P ∪ Q)})

·-distribʳ₀-⊔ : (C P Q : NeTraces) → ((P ∪ Q) · C) ≾₀ ((P · C) ∪ (Q · C))
·-distribʳ₀-⊔ C P Q =
  subst (((P ∪ Q) · C) ≾₀_) (·-distribʳ-∪ P Q C) (≾₀-refl {(P ∪ Q) · C})

-- a language product permitting nothing but the empty run has both
-- factors permitting nothing but it

≾₀-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾₀ u → P ≾₀ u
≾₀-zero-productˡ {P} {Q} rel =
  ⊑-zero-productˡ {traces P} {traces Q} (nonempty Q) (⊑-nfˡ⁻ rel)

≾₀-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾₀ u → Q ≾₀ u
≾₀-zero-productʳ {P} {Q} rel =
  ⊑-zero-productʳ {traces P} {traces Q} (nonempty P) (⊑-nfˡ⁻ rel)

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

-- there is no least grade: `{ ε }` is below only the lists naming `ε`

uᵖ-not-least : ¬ Minimum _≾_ uᵖ
uᵖ-not-least least = least (permitting (of-dur 1)) ε _

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

-- `any-run` is strictly greatest, so the mixed cases are absurd and
-- the order is antisymmetric: the two grades list the same runs

≾-antisym : {P Q : Permits} → P ≾ Q → Q ≾ P → P ≡ Q
≾-antisym {permitting P} {permitting Q} p q =
  cong permitting_ (≾₀-antisym {P} {Q} p q)
≾-antisym {permitting _} {any-run}      p ()
≾-antisym {any-run}      {permitting _} () q
≾-antisym {any-run}      {any-run}      p q  = refl

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
-- Binary joins: the union of the listed runs, with `any-run`
-- absorbing, it being the greatest grade

infixl 6 _⊔ᵖ_

_⊔ᵖ_ : Permits → Permits → Permits
(permitting P) ⊔ᵖ (permitting Q) = permitting (P ∪ Q)
(permitting _) ⊔ᵖ any-run        = any-run
any-run        ⊔ᵖ _              = any-run

⊔ᵖ-ubˡ : (P Q : Permits) → P ≾ (P ⊔ᵖ Q)
⊔ᵖ-ubˡ (permitting P) (permitting Q) = ⊔₀-ubˡ P Q
⊔ᵖ-ubˡ (permitting _) any-run        = tt
⊔ᵖ-ubˡ any-run        _              = tt

⊔ᵖ-ubʳ : (P Q : Permits) → Q ≾ (P ⊔ᵖ Q)
⊔ᵖ-ubʳ (permitting P) (permitting Q) = ⊔₀-ubʳ P Q
⊔ᵖ-ubʳ (permitting _) any-run        = tt
⊔ᵖ-ubʳ any-run        (permitting _) = tt
⊔ᵖ-ubʳ any-run        any-run        = tt

⊔ᵖ-lub : {P Q R : Permits} → P ≾ R → Q ≾ R → (P ⊔ᵖ Q) ≾ R
⊔ᵖ-lub {permitting P} {permitting Q} {permitting R} p q = ⊔₀-lub {P} {Q} {R} p q
⊔ᵖ-lub {permitting _} {permitting _} {any-run}      p q = tt
⊔ᵖ-lub {permitting _} {any-run}      {permitting _} p ()
⊔ᵖ-lub {permitting _} {any-run}      {any-run}      p q = tt
⊔ᵖ-lub {any-run}      {_}            {permitting _} () q
⊔ᵖ-lub {any-run}      {_}            {any-run}      p q = tt

·-distribˡ-⊔ : (C P Q : Permits) → (C ·ᵖ (P ⊔ᵖ Q)) ≾ ((C ·ᵖ P) ⊔ᵖ (C ·ᵖ Q))
·-distribˡ-⊔ (permitting C) (permitting P) (permitting Q) = ·-distribˡ₀-⊔ C P Q
·-distribˡ-⊔ (permitting _) (permitting _) any-run        = tt
·-distribˡ-⊔ (permitting _) any-run        _              = tt
·-distribˡ-⊔ any-run        _              _              = tt

·-distribʳ-⊔ : (C P Q : Permits) → ((P ⊔ᵖ Q) ·ᵖ C) ≾ ((P ·ᵖ C) ⊔ᵖ (Q ·ᵖ C))
·-distribʳ-⊔ (permitting C) (permitting P) (permitting Q) = ·-distribʳ₀-⊔ C P Q
·-distribʳ-⊔ (permitting _) (permitting _) any-run        = tt
·-distribʳ-⊔ (permitting _) any-run        _              = tt
·-distribʳ-⊔ any-run        (permitting _) (permitting _) = tt
·-distribʳ-⊔ any-run        (permitting _) any-run        = tt
·-distribʳ-⊔ any-run        any-run        _              = tt

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
-- The inclusion of ℕ, and deciding the order

of-durᵖ : ℕ → Permits
of-durᵖ n = permitting (of-dur n)

of-durᵖ-zero : of-durᵖ 0 ≡ uᵖ
of-durᵖ-zero = cong permitting_ of-dur-zero

of-durᵖ-plus : {m n : ℕ} → of-durᵖ (m + n) ≡ of-durᵖ m ·ᵖ of-durᵖ n
of-durᵖ-plus {m} {n} = cong permitting_ (of-dur-plus {m} {n})

infix 5 _≾?_

_≾?_ : (P Q : Permits) → Dec (P ≾ Q)
(permitting P) ≾? (permitting Q) = P ≾₀? Q
(permitting _) ≾? any-run        = yes tt
any-run        ≾? (permitting _) = no λ ()
any-run        ≾? any-run        = yes tt

------------------------------------------------------------------------
-- The grade of sets of timed traces, read as upper bounds

right-sided : Grade ℕᴰ
right-sided = posetᵍ record
  { Carrier         = Permits
  ; _·_             = _·ᵖ_
  ; u               = uᵖ
  ; ·-identityʳ     = ·ᵖ-identityʳ
  ; ·-identityˡ     = ·ᵖ-identityˡ
  ; ·-assoc         = ·ᵖ-assoc
  ; _≾_             = _≾_
  ; ⊤               = any-run
  ; ≾-⊤             = ≾-⊤
  ; u-least?        = nothing
  ; plus?           = λ _ → nothing
  ; ·-comm?         = nothing
  ; _⊔_             = _⊔ᵖ_
  ; ⊔-ubˡ           = ⊔ᵖ-ubˡ
  ; ⊔-ubʳ           = ⊔ᵖ-ubʳ
  ; ⊔-lub           = λ {P} {Q} {R} → ⊔ᵖ-lub {P} {Q} {R}
  ; ·-distribˡ-⊔-≾  = ·-distribˡ-⊔
  ; ·-distribʳ-⊔-≾  = ·-distribʳ-⊔
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; ≾-antisym       = λ {P} {Q} → ≾-antisym {P} {Q}
  ; _≾?_            = _≾?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; of-dur          = of-durᵖ
  ; of-dur-zero     = of-durᵖ-zero
  ; of-dur-plus     = λ {m} {n} → of-durᵖ-plus {m} {n}
  }
