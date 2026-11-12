------------------------------------------------------------------------
-- Antichains of timed traces as upper bounds.                        --
--                                                                    --
-- A grade is a non-empty finite set of traces, read as the bounds    --
-- within which a computation stays: writing `X` for the runs it may  --
-- have,                                                              --
--                                                                    --
--   X is graded by Q   iff   ∀ x ∈ X. ∃ q ∈ Q. x ≼ q                 --
--                                                                    --
-- that is, every run stays within one of the listed bounds. The      --
-- quantifier is universal over the runs and existential over the     --
-- set, so a longer list permits more, and the order that weakens the --
-- grade is the Hoare (lower) lift of `_≼_`:                          --
--                                                                    --
--   P ≾ Q   iff   ∀ p ∈ P. ∃ q ∈ Q. p ≼ q                            --
--                                                                    --
-- that is, every listed bound lies within one listed in `Q`. This is --
-- `↓P ⊆ ↓Q` for the sets of runs the two grades permit, so the union --
-- of two grades is their join, the closure is downward, and the      --
-- canonical form of a grade is the antichain of its `≼`-maximal      --
-- members. The carrier is the `Antichain` of `Traces.Reduced` at the --
-- converse of the order (`Order.flipᵖ`, whose minimal members are    --
-- the maximal members of this order), and the order is a partial     --
-- order.                                                             --
--                                                                    --
-- No finite list of bounds permits every run, and the carrier has    --
-- `unbounded` as a separate point: it permits any run and is         --
-- absorbing. It is distinct from the empty set of bounds, which      --
-- permits nothing and is excluded. It is the greatest grade.         --
--                                                                    --
-- `{ ε }` is the least grade, the empty run staying within every     --
-- bound, and the unit-product law holds. Both rest on the two unit   --
-- facts that a `TraceOrder` adds to the order-theoretic part used by --
-- the reduction.                                                     --
--                                                                    --
-- Given a measure of traces in durations that is additive, monotone  --
-- and `0` only at `ε` (`Closures`), no written-out grade absorbs a   --
-- product with a trace not below `ε`, a member of greatest measure   --
-- being raised. A grade below the unit is then its own Kleene plus   --
-- and any other has `unbounded`; without a measure the hints declare --
-- no Kleene plus (`upper-boundʰ`).                                   --
--                                                                    --
-- `Traces.Banked.UpperBound` instantiates the construction at the    --
-- allowance order, under which a run stays within a bound when the   --
-- operations of the bound permit those of the run and its delays     --
-- form a budget that the run spends where the bound places it.       --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

import Grades.Traces.Order as Order
import Grades.Traces.Reduced as Reduced

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Examples.Traces.Lifted.UpperBound
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (O : Order.TraceOrder T Op) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there; any?)
open import Grades.Durations.Monus T
  using (Carrier; 0ᴰ; _+ᴰ_; _≤ᴰ_; ≤ᴰ-refl; ≤ᴰ-trans; ≤ᴰ-reflexive; ≤ᴰ-antisym;
         ≤ᴰ-total; +ᴰ-comm; 0ᴰ-least; ∸-self; +-≤-∸)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Data.Maybe.Base using (just; nothing)

open import Grades.Base
open import Grades.Hints using (GradeHints; comm-≡)

open Order.TraceOrder O using (_≼_; _≼?_; ≼-refl; ≼-trans; ≼-nil; ≼-ε-inv)

-- the carrier of the written-out bounds and every law the
-- order-theoretic half supplies: the monoid, the order, its decision
-- procedure, the joins and the inclusion of durations. The
-- reduction runs at the converse order, so its minimal members are
-- this grade's maximal ones.

module R = Reduced T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans
             (Order.flipᵖ T Op (Order.TraceOrder.base O))

open R public
  renaming (_≾_ to _≾₀_; _≾?_ to _≾₀?_;
            ≾-refl to ≾₀-refl; ≾-trans to ≾₀-trans;
            ≾-antisym to ≾₀-antisym; ≾-irrelevant to ≾₀-irrelevant;
            ·-monoˡ to ·-monoˡ₀; ·-monoʳ to ·-monoʳ₀;
            ⊔-ubˡ to ⊔₀-ubˡ; ⊔-ubʳ to ⊔₀-ubʳ; ⊔-lub to ⊔₀-lub)

------------------------------------------------------------------------
-- Distributivity, read at the order
--
-- The two sides are equal antichains, so the grade's one-directional
-- law is that equation transported.

·-distribˡ₀-⊔ : (C P Q : Antichain) → (C · (P ⊔ Q)) ≾₀ ((C · P) ⊔ (C · Q))
·-distribˡ₀-⊔ C P Q =
  subst ((C · (P ⊔ Q)) ≾₀_) (·-distribˡ-⊔ C P Q) (≾₀-refl {C · (P ⊔ Q)})

·-distribʳ₀-⊔ : (C P Q : Antichain) → ((P ⊔ Q) · C) ≾₀ ((P · C) ⊔ (Q · C))
·-distribʳ₀-⊔ C P Q =
  subst (((P ⊔ Q) · C) ≾₀_) (·-distribʳ-⊔ C P Q) (≾₀-refl {(P ⊔ Q) · C})

------------------------------------------------------------------------
-- How the unit sits
--
-- `{ ε }` is the bound that permits nothing but the empty run. Being
-- below it is therefore a statement about every member of a grade, and
-- these two lemmas are that statement read in each direction.

≾₀-𝟏-inv : {P : Antichain} → P ≾₀ 𝟏 → {p : Trace} → p ∈ traces P → p ≼ ε
≾₀-𝟏-inv {P} rel {p} m with find (toWitness (rel p (fromWitness m)))
... | t , t∈𝟏 , p≼t = subst (p ≼_) (∈-[ε]⁻ t∈𝟏) p≼t

≾₀-𝟏 : {P : Antichain} → ({p : Trace} → p ∈ traces P → p ≼ ε) → P ≾₀ 𝟏
≾₀-𝟏 {P} f p m =
  fromWitness {a? = any? (_≽?_ p) (traces 𝟏)} (here (f (toWitness m)))

-- the unit is the least grade, the empty run staying within every bound

≾₀-⊥ : (P : Antichain) → 𝟏 ≾₀ P
≾₀-⊥ P s m
  with ∈-[ε]⁻ (toWitness {a? = s ∈? traces 𝟏} m)
... | refl with neHead (traces P) (nonempty P)
...           | t , t∈P =
                fromWitness (Any.map (λ eq → subst (ε ≼_) eq ≼-nil) t∈P)

------------------------------------------------------------------------
-- Unit-product property
--
-- A bound below `{ ε }` permits nothing but the empty run, and the
-- trace monoid is conical, so a product below the unit has each factor
-- below it. The reduction is transparent to the argument: a member of
-- the raw language product is itself below a member of the reduced
-- one, which the hypothesis places below `ε`.

≾₀-zero-productˡ : {P Q : Antichain} → (P · Q) ≾₀ 𝟏 → P ≾₀ 𝟏
≾₀-zero-productˡ {P} {Q} rel = ≾₀-𝟏 {P} step
  where
    step : {p : Trace} → p ∈ traces P → p ≼ ε
    step {p} m with neHead (traces Q) (nonempty Q)
    ... | y , y∈Q
            with find (n-◃⁻ (traces P ·ˢ traces Q)
                            (◃-∈ (∈-cartesianProductWith⁺ _∙_ m y∈Q)))
    ...     | r , r∈PQ , py≼r =
              subst (_≼ ε)
                    (sym (∙-conicalˡ {p} {y}
                           (≼-ε-inv (≼-trans py≼r
                                      (≾₀-𝟏-inv {P · Q} rel r∈PQ)))))
                    ≼-nil

≾₀-zero-productʳ : {P Q : Antichain} → (P · Q) ≾₀ 𝟏 → Q ≾₀ 𝟏
≾₀-zero-productʳ {P} {Q} rel = ≾₀-𝟏 {Q} step
  where
    step : {q : Trace} → q ∈ traces Q → q ≼ ε
    step {q} m with neHead (traces P) (nonempty P)
    ... | x , x∈P
            with find (n-◃⁻ (traces P ·ˢ traces Q)
                            (◃-∈ (∈-cartesianProductWith⁺ _∙_ x∈P m)))
    ...     | r , r∈PQ , xq≼r =
              subst (_≼ ε)
                    (sym (∙-conicalʳ {x} {q}
                           (≼-ε-inv (≼-trans xq≼r
                                      (≾₀-𝟏-inv {P · Q} rel r∈PQ)))))
                    ≼-nil

------------------------------------------------------------------------
-- The carrier: a written-out antichain of bounds, or no bound at all

infix 50 within_

data Bounds : Set₀ where
  within_   : Antichain → Bounds
  unbounded : Bounds

within-inj : {P Q : Antichain} → within P ≡ within Q → P ≡ Q
within-inj refl = refl

------------------------------------------------------------------------
-- The monoid: the language product, with `unbounded` absorbing

infixl 7 _·ᵇ_

_·ᵇ_ : Bounds → Bounds → Bounds
(within P) ·ᵇ (within Q) = within (P · Q)
(within _) ·ᵇ unbounded  = unbounded
unbounded  ·ᵇ _          = unbounded

𝟏ᵇ : Bounds
𝟏ᵇ = within 𝟏

·ᵇ-identityʳ : (P : Bounds) → P ·ᵇ 𝟏ᵇ ≡ P
·ᵇ-identityʳ (within P) = cong within_ (·-identityʳ P)
·ᵇ-identityʳ unbounded  = refl

·ᵇ-identityˡ : (P : Bounds) → 𝟏ᵇ ·ᵇ P ≡ P
·ᵇ-identityˡ (within P) = cong within_ (·-identityˡ P)
·ᵇ-identityˡ unbounded  = refl

·ᵇ-assoc : (P Q R : Bounds) → (P ·ᵇ Q) ·ᵇ R ≡ P ·ᵇ (Q ·ᵇ R)
·ᵇ-assoc (within P) (within Q) (within R) = cong within_ (·-assoc P Q R)
·ᵇ-assoc (within _) (within _) unbounded  = refl
·ᵇ-assoc (within _) unbounded  (within _) = refl
·ᵇ-assoc (within _) unbounded  unbounded  = refl
·ᵇ-assoc unbounded  _          _          = refl

------------------------------------------------------------------------
-- The order: the antichains' own order, with `unbounded` greatest

infix 5 _≾_

_≾_ : Bounds → Bounds → Set
(within P) ≾ (within Q) = P ≾₀ Q
(within _) ≾ unbounded  = ⊤
unbounded  ≾ (within _) = ⊥
unbounded  ≾ unbounded  = ⊤

≾-⊤ : (P : Bounds) → P ≾ unbounded
≾-⊤ (within _) = tt
≾-⊤ unbounded  = tt

-- and the unit least, `unbounded` being out of its reach

≾-⊥ : (P : Bounds) → 𝟏ᵇ ≾ P
≾-⊥ (within P) = ≾₀-⊥ P
≾-⊥ unbounded  = tt

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

------------------------------------------------------------------------
-- Antisymmetry
--
-- Mutually-permitting grades are propositionally equal, an antichain
-- being determined by the closure the order reads, and `unbounded`
-- being comparable with a written-out grade in one direction only.

≾-antisym : {P Q : Bounds} → P ≾ Q → Q ≾ P → P ≡ Q
≾-antisym {within P}  {within Q}  p q = cong within_ (≾₀-antisym {P} {Q} p q)
≾-antisym {within _}  {unbounded} p ()
≾-antisym {unbounded} {within _}  () q
≾-antisym {unbounded} {unbounded} p q = refl

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
-- Binary joins: the union of the written-out bounds, with `unbounded`
-- absorbing, it being the greatest grade

infixl 6 _⊔ᵇ_

_⊔ᵇ_ : Bounds → Bounds → Bounds
(within P) ⊔ᵇ (within Q) = within (P ⊔ Q)
(within _) ⊔ᵇ unbounded  = unbounded
unbounded  ⊔ᵇ _          = unbounded

⊔ᵇ-ubˡ : (P Q : Bounds) → P ≾ (P ⊔ᵇ Q)
⊔ᵇ-ubˡ (within P) (within Q) = ⊔₀-ubˡ P Q
⊔ᵇ-ubˡ (within _) unbounded  = tt
⊔ᵇ-ubˡ unbounded  _          = tt

⊔ᵇ-ubʳ : (P Q : Bounds) → Q ≾ (P ⊔ᵇ Q)
⊔ᵇ-ubʳ (within P) (within Q) = ⊔₀-ubʳ P Q
⊔ᵇ-ubʳ (within _) unbounded  = tt
⊔ᵇ-ubʳ unbounded  (within _) = tt
⊔ᵇ-ubʳ unbounded  unbounded  = tt

⊔ᵇ-lub : {P Q R : Bounds} → P ≾ R → Q ≾ R → (P ⊔ᵇ Q) ≾ R
⊔ᵇ-lub {within P}  {within Q}  {within R}  p q = ⊔₀-lub {P} {Q} {R} p q
⊔ᵇ-lub {within _}  {within _}  {unbounded} p q = tt
⊔ᵇ-lub {within _}  {unbounded} {within _}  p ()
⊔ᵇ-lub {within _}  {unbounded} {unbounded} p q = tt
⊔ᵇ-lub {unbounded} {_}         {within _}  () q
⊔ᵇ-lub {unbounded} {_}         {unbounded} p q = tt

·ᵇ-distribˡ-⊔ : (C P Q : Bounds) → (C ·ᵇ (P ⊔ᵇ Q)) ≾ ((C ·ᵇ P) ⊔ᵇ (C ·ᵇ Q))
·ᵇ-distribˡ-⊔ (within C) (within P) (within Q) = ·-distribˡ₀-⊔ C P Q
·ᵇ-distribˡ-⊔ (within _) (within _) unbounded  = tt
·ᵇ-distribˡ-⊔ (within _) unbounded  _          = tt
·ᵇ-distribˡ-⊔ unbounded  _          _          = tt

·ᵇ-distribʳ-⊔ : (C P Q : Bounds) → ((P ⊔ᵇ Q) ·ᵇ C) ≾ ((P ·ᵇ C) ⊔ᵇ (Q ·ᵇ C))
·ᵇ-distribʳ-⊔ (within C) (within P) (within Q) = ·-distribʳ₀-⊔ C P Q
·ᵇ-distribʳ-⊔ (within _) (within _) unbounded  = tt
·ᵇ-distribʳ-⊔ (within _) unbounded  _          = tt
·ᵇ-distribʳ-⊔ unbounded  (within _) (within _) = tt
·ᵇ-distribʳ-⊔ unbounded  (within _) unbounded  = tt
·ᵇ-distribʳ-⊔ unbounded  unbounded  _          = tt

------------------------------------------------------------------------
-- Unit-product property at the carrier
--
-- `unbounded` is above the unit and not below it, so its clauses are
-- vacuous and the property is the antichains' own.

≾-zero-productˡ : {P Q : Bounds} → (P ·ᵇ Q) ≾ 𝟏ᵇ → P ≾ 𝟏ᵇ
≾-zero-productˡ {within P}  {within Q}  p = ≾₀-zero-productˡ {P} {Q} p
≾-zero-productˡ {within _}  {unbounded} ()
≾-zero-productˡ {unbounded} {_}         ()

≾-zero-productʳ : {P Q : Bounds} → (P ·ᵇ Q) ≾ 𝟏ᵇ → Q ≾ 𝟏ᵇ
≾-zero-productʳ {within P}  {within Q}  p = ≾₀-zero-productʳ {P} {Q} p
≾-zero-productʳ {within _}  {unbounded} ()
≾-zero-productʳ {unbounded} {_}         ()

------------------------------------------------------------------------
-- The inclusion of durations, and deciding the order

ιᵇ : Carrier → Bounds
ιᵇ n = within (ι n)

ιᵇ-zero : ιᵇ 0ᴰ ≡ 𝟏ᵇ
ιᵇ-zero = cong within_ ι-zero

ιᵇ-plus : {m n : Carrier} → ιᵇ (m +ᴰ n) ≡ ιᵇ m ·ᵇ ιᵇ n
ιᵇ-plus {m} {n} = cong within_ (ι-plus {m} {n})

infix 5 _≾?_

_≾?_ : (P Q : Bounds) → Dec (P ≾ Q)
(within P) ≾? (within Q) = P ≾₀? Q
(within _) ≾? unbounded  = yes tt
unbounded  ≾? (within _) = no λ ()
unbounded  ≾? unbounded  = yes tt

------------------------------------------------------------------------
-- The grade of antichains of timed traces, read as upper bounds

upper-bound : Grade D
upper-bound = posetᵍ record
  { Carrier         = Bounds
  ; _·_             = _·ᵇ_
  ; 𝟏               = 𝟏ᵇ
  ; ·-identityʳ     = ·ᵇ-identityʳ
  ; ·-identityˡ     = ·ᵇ-identityˡ
  ; ·-assoc         = ·ᵇ-assoc
  ; _≾_             = _≾_
  ; ⊤               = unbounded
  ; ≾-⊤             = ≾-⊤
  ; _⊔_             = _⊔ᵇ_
  ; ⊔-ubˡ           = ⊔ᵇ-ubˡ
  ; ⊔-ubʳ           = ⊔ᵇ-ubʳ
  ; ⊔-lub           = λ {P} {Q} {R} → ⊔ᵇ-lub {P} {Q} {R}
  ; ·-distribˡ-⊔-≾  = ·ᵇ-distribˡ-⊔
  ; ·-distribʳ-⊔-≾  = ·ᵇ-distribʳ-⊔
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾-trans {i} {j} {k}
  ; ≾-antisym       = λ {P} {Q} → ≾-antisym {P} {Q}
  ; _≾?_            = _≾?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾-irrelevant {c} {d}
  ; ι               = ιᵇ
  ; ι-zero          = ιᵇ-zero
  ; ι-plus          = λ {m} {n} → ιᵇ-plus {m} {n}
  }

-- its hints, without closures

upper-boundʰ : GradeHints upper-bound
upper-boundʰ = record
  { 𝟏-least? = just ≾-⊥
  ; ·-comm?  = nothing
  ; plus?    = λ _ → nothing
  }

------------------------------------------------------------------------
-- Closures
--
-- Given a measure `μ` of traces, additive, monotone for `_≼_` and `0`
-- only at `ε`, no written-out grade absorbs a product with a trace not
-- below `ε`, on either side: a member of greatest measure, followed or
-- preceded by that trace, lies within no member. So a grade with a
-- member not below `ε` is absorbed by `unbounded` alone, which is its
-- closure; a grade below the unit is its own.

module Closures
  (μ   : Trace → Carrier)
  (μ-∙ : (s t : Trace) → μ (s ∙ t) ≡ μ s +ᴰ μ t)
  (μ-≼ : {s t : Trace} → s ≼ t → μ s ≤ᴰ μ t)
  (μ-ε : (s : Trace) → μ s ≡ 0ᴰ → s ≡ ε)
  where

  private
    -- a sum below one summand: the other is `0`
    absorbs : (a b : Carrier) → a +ᴰ b ≤ᴰ b → a ≡ 0ᴰ
    absorbs a b h =
      ≤ᴰ-antisym (subst (a ≤ᴰ_) (∸-self b)
                        (+-≤-∸ ≤ᴰ-refl (≤ᴰ-trans (≤ᴰ-reflexive (+ᴰ-comm b a)) h)))
                 (0ᴰ-least a)

    -- a trace not below `ε` has a positive measure
    μ-pos : {t : Trace} → ¬ (t ≼ ε) → ¬ (μ t ≡ 0ᴰ)
    μ-pos {t} ¬t e = ¬t (subst (_≼ ε) (sym (μ-ε t e)) (≼-refl ε))

    -- a member of greatest measure
    top : (x : Trace) (xs : List Trace)
        → Σ Trace λ m → m ∈ (x ∷ xs) × ({y : Trace} → y ∈ (x ∷ xs) → μ y ≤ᴰ μ m)
    top x [] = x , here refl , λ { (here refl) → ≤ᴰ-refl ; (there ()) }
    top x (x' ∷ xs) with top x' xs
    ... | m , m∈ , ub with ≤ᴰ-total (μ x) (μ m)
    ...   | inj₁ le = m , there m∈ , λ { (here refl) → le ; (there y∈) → ub y∈ }
    ...   | inj₂ ge = x , here refl , λ { (here refl) → ≤ᴰ-refl ; (there y∈) → ≤ᴰ-trans (ub y∈) ge }

    -- no non-empty list absorbs a trace not below `ε`, on the left
    no-absorbˡ : {t q : Trace} {Q : List Trace} → ¬ (t ≼ ε) → q ∈ Q
               → ¬ ({y : Trace} → y ∈ Q → (t ∙ y) ◃ Q)
    no-absorbˡ {Q = []}     _  ()
    no-absorbˡ {t} {Q = x ∷ xs} ¬t _ f with top x xs
    ... | m , m∈ , ub with find (f m∈)
    ...   | z , z∈ , tm≼z =
            μ-pos ¬t (absorbs (μ t) (μ m)
              (subst (_≤ᴰ μ m) (μ-∙ t m) (≤ᴰ-trans (μ-≼ tm≼z) (ub z∈))))

    -- ... and on the right
    no-absorbʳ : {t q : Trace} {Q : List Trace} → ¬ (t ≼ ε) → q ∈ Q
               → ¬ ({y : Trace} → y ∈ Q → (y ∙ t) ◃ Q)
    no-absorbʳ {Q = []}     _  ()
    no-absorbʳ {t} {Q = x ∷ xs} ¬t _ f with top x xs
    ... | m , m∈ , ub with find (f m∈)
    ...   | z , z∈ , mt≼z =
            μ-pos ¬t (absorbs (μ t) (μ m)
              (≤ᴰ-trans (≤ᴰ-reflexive (trans (+ᴰ-comm (μ t) (μ m)) (sym (μ-∙ m t))))
                        (≤ᴰ-trans (μ-≼ mt≼z) (ub z∈))))

    -- a product of members lies within a member of a grade above the
    -- product
    prod-◃ : {P Q R : Antichain} → (P · Q) ≾₀ R
           → {a b : Trace} → a ∈ traces P → b ∈ traces Q → (a ∙ b) ◃ traces R
    prod-◃ {P} {Q} {R} rel a∈ b∈ =
      ◃-trans {traces (P · Q)} {traces R} (λ {w} → ≾ˢ-◃ {traces (P · Q)} {traces R} rel {w})
        (n-◃⁻ (traces P ·ˢ traces Q) (◃-∈ (∈-cartesianProductWith⁺ _∙_ a∈ b∈)))

    -- a grade with no member outside `ε` is below the unit
    below-𝟏 : (P : Antichain) → ({p : Trace} → p ∈ traces P → ¬ (p ≼ ε) → ⊥) → P ≾₀ 𝟏
    below-𝟏 P f = ≾₀-𝟏 {P} step
      where
        step : {p : Trace} → p ∈ traces P → p ≼ ε
        step {p} m with p ≼? ε
        ... | yes q = q
        ... | no ¬q = ⊥-elim (f m ¬q)

  plusᵇ : (P : Bounds) → Plus _·ᵇ_ _≾_ P
  plusᵇ unbounded = plus-self tt tt
  plusᵇ (within P) with P ≾₀? 𝟏
  ... | yes r = plus-self (≾₀-refl {P})
                  (subst ((P · P) ≾₀_) (·-identityˡ P) (·-monoˡ₀ {P} {P} {𝟏} r))
  ... | no ¬r = plus unbounded tt tt least indˡ indʳ
    where
      least : {v : Bounds} → within P ≾ v → v ·ᵇ v ≾ v → unbounded ≾ v
      least {within Q} r₁ r₂ = ¬r (below-𝟏 P step)
        where
          step : {p : Trace} → p ∈ traces P → ¬ (p ≼ ε) → ⊥
          step p∈ ¬p with find (≾ˢ-◃ {traces P} {traces Q} r₁ p∈)
          ... | q , q∈ , p≼q =
                no-absorbʳ (λ q≼ε → ¬p (≼-trans p≼q q≼ε)) q∈
                  (λ y∈ → prod-◃ {Q} {Q} {Q} r₂ y∈ q∈)
      least {unbounded} _ _ = tt

      indˡ : {d : Bounds} → within P ·ᵇ d ≾ d → unbounded ·ᵇ d ≾ d
      indˡ {within Q} r = ¬r (below-𝟏 P λ p∈ ¬p →
        no-absorbˡ ¬p (proj₂ (neHead (traces Q) (nonempty Q)))
          (λ y∈ → prod-◃ {P} {Q} {Q} r p∈ y∈))
      indˡ {unbounded} _ = tt

      indʳ : {d : Bounds} → d ·ᵇ within P ≾ d → d ·ᵇ unbounded ≾ d
      indʳ {within Q} r = ¬r (below-𝟏 P λ p∈ ¬p →
        no-absorbʳ ¬p (proj₂ (neHead (traces Q) (nonempty Q)))
          (λ y∈ → prod-◃ {Q} {P} {Q} r y∈ p∈))
      indʳ {unbounded} _ = tt

  -- its hints, with closures

  upper-bound⁺ʰ : GradeHints upper-bound
  upper-bound⁺ʰ = record
    { 𝟏-least? = just ≾-⊥
    ; ·-comm?  = nothing
    ; plus?    = λ P → just (plusᵇ P)
    }
