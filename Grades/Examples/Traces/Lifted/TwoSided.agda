------------------------------------------------------------------------
-- Sets of timed traces bounding a computation from both sides.       --
--                                                                    --
-- A grade is a pair `[ P , Q ]` of antichains of traces, the floor   --
-- reduced to its weakest guarantees and the cap to its most          --
-- permissive allowances, read against the runs `X` a computation may --
-- have:                                                              --
--                                                                    --
--   ∀ x ∈ X. ∃ p ∈ P. p ≼ᶠ x     in every run, at least one of the   --
--                                listed guarantees is covered        --
--   ∀ x ∈ X. ∃ q ∈ Q. x ≼ᶜ q     and the run stays within one of the --
--                                listed allowances                   --
--                                                                    --
-- Both halves are universal over the runs and existential over the   --
-- set, so both endpoints are read disjunctively and weaken by        --
-- gaining members, and the union of two grades is their join at      --
-- either end.                                                        --
--                                                                    --
-- The construction takes the two orders `Oᶠ` and `Oᶜ` separately,    --
-- and `Example.Traces.Timed.TwoSided` instantiates them at the       --
-- incomparable `Traces.Coverage` and `Traces.Allowance`, with the    --
-- cost models `costˡᵒ` for a guarantee and `costʰⁱ` for an           --
-- allowance.                                                         --
--                                                                    --
-- The coherence field is run consistency: some run covers a listed   --
-- guarantee and stays within a listed allowance,                     --
--                                                                    --
--   ∃ p ∈ P. ∃ q ∈ Q. ∃ x. p ≼ᶠ x × x ≼ᶜ q                           --
--                                                                    --
-- decided by `consistent?`, a parameter. The condition is necessary  --
-- for the grade to admit any run. Durations being monotone along     --
-- both orders, and a run's floor measure below its cap measure, it   --
-- implies the condition `min ≤ max` required by the projection to    --
-- time intervals (`◇ˢ₀-dur`).                                        --
--                                                                    --
-- The greatest grade is `[ u , unbounded ]`, the unit of the floor   --
-- under the unbounded allowance of the cap. It is not absorbing.     --
------------------------------------------------------------------------

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Decidable; DecidableEquality; Minimum; Transitive; Trichotomous)

open import Util.Equality

import Grades.Traces.Base as Base
import Grades.Traces.Durations as Dur
import Grades.Traces.Order as Order

open import Data.Product using (Σ; _×_)
open import Relation.Nullary using (Dec)

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Examples.Traces.Lifted.TwoSided
  {D : Duration} (T : TimeDomain D) (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ costʰⁱ : Op → Duration.Carrier D)
  (cost-≤ : (o : Op) → TimeDomain._≤ᴰ_ T (costˡᵒ o) (costʰⁱ o))
  (Oᶠ Oᶜ : Order.TraceOrder T Op)
  (durᶠ : {s t : Base.Trace T Op}
        → Order.TraceOrder._≼_ Oᶠ s t
        → TimeDomain._≤ᴰ_ T (Dur.Durations.duration T Op costˡᵒ s)
                             (Dur.Durations.duration T Op costˡᵒ t))
  (durᶜ : {s t : Base.Trace T Op}
        → Order.TraceOrder._≼_ Oᶜ s t
        → TimeDomain._≤ᴰ_ T (Dur.Durations.duration T Op costʰⁱ s)
                             (Dur.Durations.duration T Op costʰⁱ t))
  -- whether a guarantee and an allowance admit a common run
  (consistent? : (p q : Base.Trace T Op)
               → Dec (Σ (Base.Trace T Op) (λ x → Order.TraceOrder._≼_ Oᶠ p x
                                               × Order.TraceOrder._≼_ Oᶜ x q)))
  where

open import Data.List.Base using (List; _++_)
open import Data.Unit using (⊤; tt)
open import Grades.Durations.Monus T as M using (Carrier; 0ᴰ; _<ᴰ_)
open M.Notation using (_≤_; ≤-trans)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (¬_; Dec)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_)

open import Data.Maybe.Base using (nothing)

open import Grades.Base

open import Grades.Traces.Sets T Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Grades.Traces.Durations T Op

-- each endpoint is ordered exactly as the corresponding one-sided grade
-- orders it, at its own order

open import Grades.Examples.Traces.Lifted.LeftSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans Oᶠ
  using (Antichain)
  renaming (traces to tracesˡᵒ; nonempty to nonemptyˡᵒ;
            n to nˡᵒ; n-◃⁻ to nˡᵒ-◃⁻; ◃-∈ to ◃ˡᵒ-∈;
            _·_ to _·ˡᵒ_; u to uˡᵒ; _⊔_ to _⊔ˡᵒ_;
            ·-identityʳ to ·ˡᵒ-identityʳ; ·-identityˡ to ·ˡᵒ-identityˡ;
            ·-assoc to ·ˡᵒ-assoc;
            of-dur to of-durˡᵒ; of-dur-zero to of-durˡᵒ-zero;
            of-dur-plus to of-durˡᵒ-plus;
            _≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_; ≾-⊤ to ≾ˡᵒ-⊤;
            u⋠of-dur to uˡᵒ⋠of-durˡᵒ;
            ≾-refl to ≾ˡᵒ-refl; ≾-trans to ≾ˡᵒ-trans;
            ·-monoˡ to ·ˡᵒ-monoˡ; ·-monoʳ to ·ˡᵒ-monoʳ;
            ≾-zero-productˡ to ≾ˡᵒ-zero-productˡ;
            ≾-zero-productʳ to ≾ˡᵒ-zero-productʳ;
            ≾-irrelevant to ≾ˡᵒ-irrelevant; ≾-antisym to ≾ˡᵒ-antisym;
            ⊔-ubˡ to ⊔ˡᵒ-ubˡ; ⊔-ubʳ to ⊔ˡᵒ-ubʳ; ⊔-lub to ⊔ˡᵒ-lub;
            ·-distribˡ-⊔-≾ to ·ˡᵒ-distribˡ-⊔;
            ·-distribʳ-⊔-≾ to ·ˡᵒ-distribʳ-⊔)

-- the cap's endpoint is `Bounds`, whose `unbounded` is the allowance
-- grade's own greatest element

open import Grades.Examples.Traces.Lifted.RightSided
  T Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans Oᶜ
  using (Bounds; within_; unbounded; _·ᵇ_; uᵇ; _⊔ᵇ_;
         ·ᵇ-identityʳ; ·ᵇ-identityˡ; ·ᵇ-assoc)
  renaming (Antichain to Antichainʰⁱ; traces to tracesʰⁱ;
            u to uʰⁱ; n to nʰⁱ; n-◃⁻ to nʰⁱ-◃⁻; ◃-∈ to ◃ʰⁱ-∈;
            of-dur to of-durʰⁱ; of-dur-zero to of-durʰⁱ-zero;
            of-dur-plus to of-durʰⁱ-plus;
            _≾₀_ to _≾ʰⁱ₀_;
            _≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_;
            ≾-refl to ≾ʰⁱ-refl; ≾-trans to ≾ʰⁱ-trans; ≾-⊤ to ≾ʰⁱ-⊤;
            ≾-antisym to ≾ʰⁱ-antisym;
            ·-monoˡ to ·ʰⁱ-monoˡ; ·-monoʳ to ·ʰⁱ-monoʳ;
            ≾-zero-productˡ to ≾ʰⁱ-zero-productˡ;
            ≾-zero-productʳ to ≾ʰⁱ-zero-productʳ;
            ≾-irrelevant to ≾ʰⁱ-irrelevant;
            ⊔ᵇ-ubˡ to ⊔ʰⁱ-ubˡ; ⊔ᵇ-ubʳ to ⊔ʰⁱ-ubʳ; ⊔ᵇ-lub to ⊔ʰⁱ-lub;
            ·ᵇ-distribˡ-⊔ to ·ʰⁱ-distribˡ-⊔;
            ·ᵇ-distribʳ-⊔ to ·ʰⁱ-distribʳ-⊔)

-- each endpoint is measured at its own cost model

-- the two orders on traces

open Order.TraceOrder Oᶠ using ()
  renaming (_≼_ to _≼ᶠ_; ≼-refl to ≼ᶠ-refl; ≼-trans to ≼ᶠ-trans;
            mono-∙ to ≼ᶠ-mono-∙)
open Order.TraceOrder Oᶜ using ()
  renaming (_≼_ to _≼ᶜ_; ≼-refl to ≼ᶜ-refl; ≼-trans to ≼ᶜ-trans;
            mono-∙ to ≼ᶜ-mono-∙)

-- a run that covers the guarantee `p` and stays within the allowance `q`

Consistent : Trace → Trace → Set
Consistent p q = Σ Trace (λ x → p ≼ᶠ x × x ≼ᶜ q)

open Durations costˡᵒ using ()
  renaming (duration to durationˡᵒ)
open Durations costʰⁱ using ()
  renaming (duration to durationʰⁱ)

-- a trace's floor measure is below its cap measure

durationˡᵒ≤ʰⁱ : (t : Trace) → durationˡᵒ t ≤ durationʰⁱ t
durationˡᵒ≤ʰⁱ = duration-mono costˡᵒ costʰⁱ cost-≤

------------------------------------------------------------------------
-- Run consistency
--
-- `xs ◇ˢ₀ ys` says some trace of `xs` and some trace of `ys` admit a
-- common run: one that covers the first and stays within the second.
-- It is decided, hence irrelevant.

infix 5 _◇ˢ₀_

_◇ˢ₀_ : List Trace → List Trace → Set
xs ◇ˢ₀ ys = True (any? (λ p → any? (λ q → consistent? p q) ys) xs)

◇ˢ₀-irr : {xs ys : List Trace} → (p q : xs ◇ˢ₀ ys) → p ≡ q
◇ˢ₀-irr {xs} {ys} = True-irr (any? (λ p → any? (λ q → consistent? p q) ys) xs)

-- introduced by a pair of members and a run, and eliminated into one

◇ˢ₀-intro : {xs ys : List Trace} {p q : Trace}
          → p ∈ xs → q ∈ ys → Consistent p q → xs ◇ˢ₀ ys
◇ˢ₀-intro p∈ q∈ c =
  fromWitness (Any.map (λ { refl → Any.map (λ { refl → c }) q∈ }) p∈)

record Witness (xs ys : List Trace) : Set where
  constructor witness
  field
    {wˡᵒ wʰⁱ} : Trace
    wˡᵒ∈      : wˡᵒ ∈ xs
    wʰⁱ∈      : wʰⁱ ∈ ys
    run       : Consistent wˡᵒ wʰⁱ

◇ˢ₀-elim : {xs ys : List Trace} → xs ◇ˢ₀ ys → Witness xs ys
◇ˢ₀-elim p with find (toWitness p)
... | _ , p∈ , hit with find hit
...   | _ , q∈ , c = witness p∈ q∈ c

-- the run's durations sit between the two, so the guarantee takes no
-- longer than the allowance: run consistency gives `min ≤ max`

consistent-dur : {p q : Trace} → Consistent p q → durationˡᵒ p ≤ durationʰⁱ q
consistent-dur (x , px , xq) =
  ≤-trans (durᶠ px) (≤-trans (durationˡᵒ≤ʰⁱ x) (durᶜ xq))

◇ˢ₀-dur : {xs ys : List Trace} → xs ◇ˢ₀ ys
        → Any (λ p → Any (λ q → durationˡᵒ p ≤ durationʰⁱ q) ys) xs
◇ˢ₀-dur p with ◇ˢ₀-elim p
... | witness p∈ q∈ c =
      Any.map (λ { refl → Any.map (λ { refl → consistent-dur c }) q∈ }) p∈

-- against `unbounded` there is nothing to ask beyond a guarantee, which
-- every grade has: the guarantee itself is a run within no bound

infix 5 _◇ˢ_

_◇ˢ_ : List Trace → Bounds → Set
xs ◇ˢ (within Q) = xs ◇ˢ₀ tracesʰⁱ Q
xs ◇ˢ unbounded  = ⊤

◇ˢ-irr : {xs : List Trace} {Y : Bounds} → (p q : xs ◇ˢ Y) → p ≡ q
◇ˢ-irr {xs} {within Q}  = ◇ˢ₀-irr {xs} {tracesʰⁱ Q}
◇ˢ-irr {xs} {unbounded} tt tt = refl

-- a set is consistent with itself under either reading, at whichever
-- member is to hand: the member is its own run

◇ˢ₀-self : (xs : List Trace) → NonEmpty xs → xs ◇ˢ₀ xs
◇ˢ₀-self xs ne with neHead xs ne
... | t , t∈xs = ◇ˢ₀-intro t∈xs t∈xs (t , ≼ᶠ-refl t , ≼ᶜ-refl t)

-- a witness travels along any map that keeps the members --
-- normalisation in particular

◇ˢ₀-∈ : {xs xs' ys ys' : List Trace}
      → ({w : Trace} → w ∈ xs → w ∈ xs')
      → ({w : Trace} → w ∈ ys → w ∈ ys')
      → xs ◇ˢ₀ ys → xs' ◇ˢ₀ ys'
◇ˢ₀-∈ f g p with ◇ˢ₀-elim p
... | witness p∈ q∈ c = ◇ˢ₀-intro (f p∈) (g q∈) c

-- reducing the floor keeps it: the witnessing guarantee is replaced by
-- one below it, which the run still covers

◇ˢ₀-nˡ : {xs ys : List Trace} → xs ◇ˢ₀ ys → nˡᵒ xs ◇ˢ₀ ys
◇ˢ₀-nˡ {xs} p with ◇ˢ₀-elim p
... | witness p∈ q∈ (x , px , xq)
        with find (nˡᵒ-◃⁻ xs (◃ˡᵒ-∈ p∈))
...     | _ , p'∈n , p'≼p = ◇ˢ₀-intro p'∈n q∈ (x , ≼ᶠ-trans p'≼p px , xq)

-- reducing the cap keeps it too: the witnessing allowance is replaced
-- by one above it, which the run still stays within

◇ˢ₀-nʰⁱ : {xs ys : List Trace} → xs ◇ˢ₀ ys → xs ◇ˢ₀ nʰⁱ ys
◇ˢ₀-nʰⁱ {xs} {ys} p with ◇ˢ₀-elim p
... | witness p∈ q∈ (x , px , xq)
        with find (nʰⁱ-◃⁻ ys (◃ʰⁱ-∈ q∈))
...     | _ , q'∈n , q≼q' = ◇ˢ₀-intro p∈ q'∈n (x , px , ≼ᶜ-trans xq q≼q')

-- both endpoints of a compound grade are reduced

◇ˢ₀-n-n : {xs ys : List Trace} → xs ◇ˢ₀ ys → nˡᵒ xs ◇ˢ₀ nʰⁱ ys
◇ˢ₀-n-n {xs} {ys} p = ◇ˢ₀-nʰⁱ {nˡᵒ xs} {ys} (◇ˢ₀-nˡ {xs} {ys} p)

-- consistency survives the language product: the two runs are
-- sequenced

◇ˢ₀-·ˢ : {xs xs' ys ys' : List Trace}
       → xs ◇ˢ₀ ys → xs' ◇ˢ₀ ys' → (xs ·ˢ xs') ◇ˢ₀ (ys ·ˢ ys')
◇ˢ₀-·ˢ p q with ◇ˢ₀-elim p | ◇ˢ₀-elim q
... | witness p∈ q∈ (x , px , xq) | witness p'∈ q'∈ (x' , px' , xq') =
      ◇ˢ₀-intro (∈-cartesianProductWith⁺ _∙_ p∈ p'∈)
                (∈-cartesianProductWith⁺ _∙_ q∈ q'∈)
                (x ∙ x' , ≼ᶠ-mono-∙ px px' , ≼ᶜ-mono-∙ xq xq')

◇ˢ-·ˢ : {xs xs' : List Trace} {Y Y' : Bounds}
      → xs ◇ˢ Y → xs' ◇ˢ Y' → nˡᵒ (xs ·ˢ xs') ◇ˢ (Y ·ᵇ Y')
◇ˢ-·ˢ {xs} {xs'} {within Q} {within Q'} p q =
  ◇ˢ₀-n-n {xs ·ˢ xs'} {tracesʰⁱ Q ·ˢ tracesʰⁱ Q'}
          (◇ˢ₀-·ˢ {xs} {xs'} {tracesʰⁱ Q} {tracesʰⁱ Q'} p q)
◇ˢ-·ˢ {_}  {_}   {within _}  {unbounded} _ _ = tt
◇ˢ-·ˢ {_}  {_}   {unbounded} {_}         _ _ = tt

-- and it survives the union at both endpoints: the witnessing pair of
-- the left-hand sets is still a pair of members

◇ˢ₀-++ : {xs xs' ys ys' : List Trace}
       → xs ◇ˢ₀ ys → (xs ++ xs') ◇ˢ₀ (ys ++ ys')
◇ˢ₀-++ {xs} {xs'} {ys} {ys'} =
  ◇ˢ₀-∈ (λ {w} → ∈-++⁺ˡ {xs = xs} {ys = xs'})
        (λ {w} → ∈-++⁺ˡ {xs = ys} {ys = ys'})

◇ˢ-⊔ᵇ : {xs xs' : List Trace} {Y Y' : Bounds}
      → xs ◇ˢ Y → nˡᵒ (xs ++ xs') ◇ˢ (Y ⊔ᵇ Y')
◇ˢ-⊔ᵇ {xs} {xs'} {within Q} {within Q'} p =
  ◇ˢ₀-n-n {xs ++ xs'} {tracesʰⁱ Q ++ tracesʰⁱ Q'}
          (◇ˢ₀-++ {xs} {xs'} {tracesʰⁱ Q} {tracesʰⁱ Q'} p)
◇ˢ-⊔ᵇ {_}  {_}   {within _}  {unbounded} _ = tt
◇ˢ-⊔ᵇ {_}  {_}   {unbounded} {_}         _ = tt

------------------------------------------------------------------------
-- The carrier

record TwoSided : Set where
  constructor [_,_]
  field
    lo : Antichain
    hi : Bounds
    -- some run covers a listed guarantee and stays within a listed
    -- allowance; implicit, as it reduces to `⊤` at concrete endpoints
    {lo◇hi} : tracesˡᵒ lo ◇ˢ hi

open TwoSided public

eqᵗˢ : {i₁ i₂ : TwoSided} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵗˢ {[ L , U ] {p}} {[ .L , .U ] {q}} refl refl =
  cong (λ c → [ L , U ] {c}) (◇ˢ-irr {tracesˡᵒ L} {U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵗˢ_

_·ᵗˢ_ : TwoSided → TwoSided → TwoSided
i₁ ·ᵗˢ i₂ =
  [ lo i₁ ·ˡᵒ lo i₂
  , hi i₁ ·ᵇ hi i₂
  ] {◇ˢ-·ˢ {tracesˡᵒ (lo i₁)} {tracesˡᵒ (lo i₂)} {hi i₁} {hi i₂}
          (lo◇hi i₁) (lo◇hi i₂)}

uᵗˢ : TwoSided
uᵗˢ = [ uˡᵒ , within uʰⁱ ] {◇ˢ₀-self (tracesˡᵒ uˡᵒ) tt}

-- the greatest grade: the weakest guarantee, which is the unit, under
-- an unbounded allowance

⊤ᵗˢ : TwoSided
⊤ᵗˢ = [ uˡᵒ , unbounded ]

·ᵗˢ-identityʳ : (i : TwoSided) → (i ·ᵗˢ uᵗˢ) ≡ i
·ᵗˢ-identityʳ i = eqᵗˢ (·ˡᵒ-identityʳ (lo i)) (·ᵇ-identityʳ (hi i))

·ᵗˢ-identityˡ : (i : TwoSided) → (uᵗˢ ·ᵗˢ i) ≡ i
·ᵗˢ-identityˡ i = eqᵗˢ (·ˡᵒ-identityˡ (lo i)) (·ᵇ-identityˡ (hi i))

·ᵗˢ-assoc : (i₁ i₂ i₃ : TwoSided)
          → ((i₁ ·ᵗˢ i₂) ·ᵗˢ i₃) ≡ (i₁ ·ᵗˢ (i₂ ·ᵗˢ i₃))
·ᵗˢ-assoc i₁ i₂ i₃ =
  eqᵗˢ (·ˡᵒ-assoc (lo i₁) (lo i₂) (lo i₃))
       (·ᵇ-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: each endpoint at its own order

infix 5 _≾ᵗˢ_

_≾ᵗˢ_ : TwoSided → TwoSided → Set
i₁ ≾ᵗˢ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

≾ᵗˢ-refl : {i : TwoSided} → i ≾ᵗˢ i
≾ᵗˢ-refl {i} = ≾ˡᵒ-refl {lo i} , ≾ʰⁱ-refl {hi i}

≾ᵗˢ-⊤ : (i : TwoSided) → i ≾ᵗˢ ⊤ᵗˢ
≾ᵗˢ-⊤ i = ≾ˡᵒ-⊤ (lo i) , ≾ʰⁱ-⊤ (hi i)

≾ᵗˢ-trans : {i₁ i₂ i₃ : TwoSided} → i₁ ≾ᵗˢ i₂ → i₂ ≾ᵗˢ i₃ → i₁ ≾ᵗˢ i₃
≾ᵗˢ-trans {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ≾ˡᵒ-trans {lo i₁} {lo i₂} {lo i₃} l₁ l₂
  , ≾ʰⁱ-trans {hi i₁} {hi i₂} {hi i₃} h₁ h₂

·ᵗˢ-monoˡ : {c i₁ i₂ : TwoSided} → i₁ ≾ᵗˢ i₂ → (i₁ ·ᵗˢ c) ≾ᵗˢ (i₂ ·ᵗˢ c)
·ᵗˢ-monoˡ {c} {i₁} {i₂} (l , h) =
    ·ˡᵒ-monoˡ {lo c} {lo i₁} {lo i₂} l
  , ·ʰⁱ-monoˡ {hi c} {hi i₁} {hi i₂} h

·ᵗˢ-monoʳ : {c i₁ i₂ : TwoSided} → i₁ ≾ᵗˢ i₂ → (c ·ᵗˢ i₁) ≾ᵗˢ (c ·ᵗˢ i₂)
·ᵗˢ-monoʳ {c} {i₁} {i₂} (l , h) =
    ·ˡᵒ-monoʳ {lo c} {lo i₁} {lo i₂} l
  , ·ʰⁱ-monoʳ {hi c} {hi i₁} {hi i₂} h

------------------------------------------------------------------------
-- Binary joins: the union at each endpoint
--
-- Both endpoints are read disjunctively, so both join by union, and
-- the coherence field of the joined pair is witnessed by the left
-- pair's own witness.

infixl 6 _⊔ᵗˢ_

_⊔ᵗˢ_ : TwoSided → TwoSided → TwoSided
i₁ ⊔ᵗˢ i₂ =
  [ lo i₁ ⊔ˡᵒ lo i₂
  , hi i₁ ⊔ᵇ hi i₂
  ] {◇ˢ-⊔ᵇ {tracesˡᵒ (lo i₁)} {tracesˡᵒ (lo i₂)} {hi i₁} {hi i₂} (lo◇hi i₁)}

⊔ᵗˢ-ubˡ : (i₁ i₂ : TwoSided) → i₁ ≾ᵗˢ (i₁ ⊔ᵗˢ i₂)
⊔ᵗˢ-ubˡ i₁ i₂ = ⊔ˡᵒ-ubˡ (lo i₁) (lo i₂) , ⊔ʰⁱ-ubˡ (hi i₁) (hi i₂)

⊔ᵗˢ-ubʳ : (i₁ i₂ : TwoSided) → i₂ ≾ᵗˢ (i₁ ⊔ᵗˢ i₂)
⊔ᵗˢ-ubʳ i₁ i₂ = ⊔ˡᵒ-ubʳ (lo i₁) (lo i₂) , ⊔ʰⁱ-ubʳ (hi i₁) (hi i₂)

⊔ᵗˢ-lub : {i₁ i₂ i₃ : TwoSided} → i₁ ≾ᵗˢ i₃ → i₂ ≾ᵗˢ i₃ → (i₁ ⊔ᵗˢ i₂) ≾ᵗˢ i₃
⊔ᵗˢ-lub {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ⊔ˡᵒ-lub {lo i₁} {lo i₂} {lo i₃} l₁ l₂
  , ⊔ʰⁱ-lub {hi i₁} {hi i₂} {hi i₃} h₁ h₂

·ᵗˢ-distribˡ-⊔ : (c i₁ i₂ : TwoSided)
               → (c ·ᵗˢ (i₁ ⊔ᵗˢ i₂)) ≾ᵗˢ ((c ·ᵗˢ i₁) ⊔ᵗˢ (c ·ᵗˢ i₂))
·ᵗˢ-distribˡ-⊔ c i₁ i₂ =
    ·ˡᵒ-distribˡ-⊔ (lo c) (lo i₁) (lo i₂)
  , ·ʰⁱ-distribˡ-⊔ (hi c) (hi i₁) (hi i₂)

·ᵗˢ-distribʳ-⊔ : (c i₁ i₂ : TwoSided)
               → ((i₁ ⊔ᵗˢ i₂) ·ᵗˢ c) ≾ᵗˢ ((i₁ ·ᵗˢ c) ⊔ᵗˢ (i₂ ·ᵗˢ c))
·ᵗˢ-distribʳ-⊔ c i₁ i₂ =
    ·ˡᵒ-distribʳ-⊔ (lo c) (lo i₁) (lo i₂)
  , ·ʰⁱ-distribʳ-⊔ (hi c) (hi i₁) (hi i₂)

------------------------------------------------------------------------
-- The coherence field travels along the order
--
-- Weakening replaces the witnessing guarantee by one below it, which
-- the run still covers, and the witnessing allowance by one above it,
-- which the run still stays within. So nothing the order reaches is
-- refused by the field.

◇ˢ₀-≾ : (P : Antichain) (Q : Antichainʰⁱ) (L : Antichain) (U : Antichainʰⁱ)
      → tracesˡᵒ P ◇ˢ₀ tracesʰⁱ Q
      → P ≾ˡᵒ L → Q ≾ʰⁱ₀ U
      → tracesˡᵒ L ◇ˢ₀ tracesʰⁱ U
◇ˢ₀-≾ P Q L U coh l h with ◇ˢ₀-elim coh
... | witness p∈ q∈ (x , px , xq)
        with find (toWitness (l _ (fromWitness p∈)))
...     | _ , p'∈L , p'≼p
            with find (toWitness (h _ (fromWitness q∈)))
...         | _ , q'∈U , q≼q' =
              ◇ˢ₀-intro p'∈L q'∈U (x , ≼ᶠ-trans p'≼p px , ≼ᶜ-trans xq q≼q')

-- an unbounded allowance asks nothing, and a bounded one can only be
-- reached from a bounded one

◇ˢ-≾ : (i : TwoSided) (L : Antichain) (U : Bounds)
     → lo i ≾ˡᵒ L → hi i ≾ʰⁱ U
     → tracesˡᵒ L ◇ˢ U
◇ˢ-≾ i L unbounded  l h = tt
◇ˢ-≾ i L (within U) l h with hi i | lo◇hi i | h
... | within Q | coh | h' = ◇ˢ₀-≾ (lo i) Q L U coh l h'

------------------------------------------------------------------------
-- Antisymmetry
--
-- Both endpoints are antisymmetric, and the coherence field is
-- irrelevant, so mutually-weakening grades are propositionally equal.

≾ᵗˢ-antisym : {i₁ i₂ : TwoSided} → i₁ ≾ᵗˢ i₂ → i₂ ≾ᵗˢ i₁ → i₁ ≡ i₂
≾ᵗˢ-antisym {i₁} {i₂} (l₁ , h₁) (l₂ , h₂) =
  eqᵗˢ (≾ˡᵒ-antisym {lo i₁} {lo i₂} l₁ l₂)
       (≾ʰⁱ-antisym {hi i₁} {hi i₂} h₁ h₂)

------------------------------------------------------------------------
-- Zero-product property
--
-- Only the cap carries information at the unit, the floor half being
-- vacuous.

≾ᵗˢ-zero-productˡ : {i₁ i₂ : TwoSided} → (i₁ ·ᵗˢ i₂) ≾ᵗˢ uᵗˢ → i₁ ≾ᵗˢ uᵗˢ
≾ᵗˢ-zero-productˡ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productˡ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productˡ {hi i₁} {hi i₂} h

≾ᵗˢ-zero-productʳ : {i₁ i₂ : TwoSided} → (i₁ ·ᵗˢ i₂) ≾ᵗˢ uᵗˢ → i₂ ≾ᵗˢ uᵗˢ
≾ᵗˢ-zero-productʳ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productʳ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productʳ {hi i₁} {hi i₂} h

≾ᵗˢ-irrelevant : {i₁ i₂ : TwoSided} → (p q : i₁ ≾ᵗˢ i₂) → p ≡ q
≾ᵗˢ-irrelevant {i₁} {i₂} (l , h) (l' , h') =
  cong₂ _,_ (≾ˡᵒ-irrelevant {lo i₁} {lo i₂} l l')
            (≾ʰⁱ-irrelevant {hi i₁} {hi i₂} h h')

------------------------------------------------------------------------
-- Including durations, and deciding the order

of-durᵗˢ : Carrier → TwoSided
of-durᵗˢ n =
  [ of-durˡᵒ n , within (of-durʰⁱ n) ] {◇ˢ₀-self (tracesˡᵒ (of-durˡᵒ n)) tt}

infix 5 _≾ᵗˢ?_

_≾ᵗˢ?_ : (i₁ i₂ : TwoSided) → Dec (i₁ ≾ᵗˢ i₂)
i₁ ≾ᵗˢ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

-- the unit is not least, once some duration is positive, its floor
-- being greatest among floors

uᵗˢ-not-least : (τ : Carrier) → 0ᴰ <ᴰ τ → ¬ Minimum _≾ᵗˢ_ uᵗˢ
uᵗˢ-not-least τ pos least = uˡᵒ⋠of-durˡᵒ τ pos (proj₁ (least (of-durᵗˢ τ)))

------------------------------------------------------------------------
-- The grade of two-sided trace intervals

two-sided : Grade D
two-sided = posetᵍ record
  { Carrier         = TwoSided
  ; _·_             = _·ᵗˢ_
  ; u               = uᵗˢ
  ; ·-identityʳ     = ·ᵗˢ-identityʳ
  ; ·-identityˡ     = ·ᵗˢ-identityˡ
  ; ·-assoc         = ·ᵗˢ-assoc
  ; _≾_             = _≾ᵗˢ_
  ; ⊤               = ⊤ᵗˢ
  ; ≾-⊤             = ≾ᵗˢ-⊤
  ; _⊔_             = _⊔ᵗˢ_
  ; ⊔-ubˡ           = ⊔ᵗˢ-ubˡ
  ; ⊔-ubʳ           = ⊔ᵗˢ-ubʳ
  ; ⊔-lub           = λ {i₁} {i₂} {i₃} → ⊔ᵗˢ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾  = ·ᵗˢ-distribˡ-⊔
  ; ·-distribʳ-⊔-≾  = ·ᵗˢ-distribʳ-⊔
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵗˢ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵗˢ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗˢ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗˢ-trans {i} {j} {k}
  ; ≾-antisym       = λ {i} {j} → ≾ᵗˢ-antisym {i} {j}
  ; _≾?_            = _≾ᵗˢ?_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗˢ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗˢ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵗˢ-irrelevant {c} {d}
  ; of-dur          = of-durᵗˢ
  ; of-dur-zero     = eqᵗˢ of-durˡᵒ-zero (cong within_ of-durʰⁱ-zero)
  ; of-dur-plus     = λ {m} {n} →
                        eqᵗˢ (of-durˡᵒ-plus {m} {n})
                             (cong within_ (of-durʰⁱ-plus {m} {n}))
  }
