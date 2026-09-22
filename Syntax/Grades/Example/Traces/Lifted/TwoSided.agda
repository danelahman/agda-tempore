------------------------------------------------------------------------
-- Sets of timed traces bounding a computation from both sides.        --
--                                                                     --
-- A grade is a pair `[ P , Q ]` of antichains of traces -- the floor  --
-- cut down to its weakest guarantees, the cap to its most permissive  --
-- allowances -- read against the runs `X` a computation may have:     --
--                                                                     --
--   ∀ x ∈ X. ∃ p ∈ P. p ≼ᶠ x     whatever happened, at least one of   --
--                                the listed guarantees was covered    --
--   ∀ x ∈ X. ∃ q ∈ Q. x ≼ᶜ q     and it stayed within one of the      --
--                                listed allowances                    --
--                                                                     --
-- Both halves are universal over the runs and existential over the    --
-- set, so both endpoints are read disjunctively, both weaken by       --
-- gaining members, and the union of two grades is their join at       --
-- either end -- the shape a branching construct wants.                --
--                                                                     --
-- The endpoints take different orders -- a guarantee needs one in     --
-- which time never buys an operation, an allowance one in which a     --
-- listed delay is a budget that buys them -- so the construction      --
-- takes `Oᶠ` and `Oᶜ` separately, and `Example.Traces.Timed.TwoSided` --
-- instantiates them at the incomparable `Traces.Coverage` and         --
-- `Traces.Allowance`. They take different cost models for the same    --
-- reason: `costˡᵒ` for a guarantee, `costʰⁱ` for an allowance, which  --
-- is why the coherence field needs `cost-≤` to compare them.          --
--                                                                     --
-- The coherence field asks that some listed guarantee take no longer  --
-- than some listed allowance: necessary for the grade to admit any    --
-- run, and exactly the `min ≤ max` the projection to time intervals   --
-- needs.                                                              --
--                                                                     --
-- The greatest grade is `[ u , unbounded ]`, the floor's unit under   --
-- the cap's unbounded allowance. It is not absorbing.                 --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Decidable; DecidableEquality; Transitive; Trichotomous)

open import Util.Equality

import Syntax.Grades.Traces.Base as Base
import Syntax.Grades.Traces.Durations as Dur
import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
  (_<ᵒ_ : Rel Op lzero)
  (<ᵒ-cmp : Trichotomous _≡_ _<ᵒ_) (<ᵒ-trans : Transitive _<ᵒ_)
  (costˡᵒ costʰⁱ : Op → ℕ)
  (cost-≤ : (o : Op) → costˡᵒ o ≤ costʰⁱ o)
  (Oᶠ Oᶜ : Order.TraceOrder Op)
  (durᶠ : {s t : Base.Trace Op}
        → Order.TraceOrder._≼_ Oᶠ s t
        → Dur.Durations.duration Op costˡᵒ s ≤ Dur.Durations.duration Op costˡᵒ t)
  (durᶜ : {s t : Base.Trace Op}
        → Order.TraceOrder._≼_ Oᶜ s t
        → Dur.Durations.duration Op costʰⁱ s ≤ Dur.Durations.duration Op costʰⁱ t)
  where

open import Data.List.Base using (List; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-++⁺ˡ)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op _<ᵒ_ <ᵒ-cmp <ᵒ-trans
open import Syntax.Grades.Traces.Durations Op

-- each endpoint is ordered exactly as the corresponding one-sided grade
-- orders it, at its own order

open import Syntax.Grades.Example.Traces.Lifted.LeftSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans Oᶠ
  using (Antichain)
  renaming (traces to tracesˡᵒ; nonempty to nonemptyˡᵒ;
            n to nˡᵒ; n-◃⁻ to nˡᵒ-◃⁻; ◃-∈ to ◃ˡᵒ-∈;
            _·_ to _·ˡᵒ_; u to uˡᵒ; _⊔_ to _⊔ˡᵒ_; _≟ᴬ_ to _≟ˡᵒ_;
            ·-identityʳ to ·ˡᵒ-identityʳ; ·-identityˡ to ·ˡᵒ-identityˡ;
            ·-assoc to ·ˡᵒ-assoc;
            of-nat to of-natˡᵒ; of-nat-zero to of-natˡᵒ-zero;
            of-nat-plus to of-natˡᵒ-plus;
            _≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_; ≾-⊤ to ≾ˡᵒ-⊤;
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

open import Syntax.Grades.Example.Traces.Lifted.RightSided
  Op _≟ₒ_ _<ᵒ_ <ᵒ-cmp <ᵒ-trans Oᶜ
  using (Bounds; within_; unbounded; _·ᵇ_; uᵇ; _≟ᴮ_; _⊔ᵇ_;
         ·ᵇ-identityʳ; ·ᵇ-identityˡ; ·ᵇ-assoc)
  renaming (Antichain to Antichainʰⁱ; traces to tracesʰⁱ;
            u to uʰⁱ; n to nʰⁱ; n-◃⁻ to nʰⁱ-◃⁻; ◃-∈ to ◃ʰⁱ-∈;
            of-nat to of-natʰⁱ; of-nat-zero to of-natʰⁱ-zero;
            of-nat-plus to of-natʰⁱ-plus;
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

open Durations costˡᵒ using ()
  renaming (duration to durationˡᵒ; duration-∙ to duration-∙ˡᵒ)
open Durations costʰⁱ using ()
  renaming (duration to durationʰⁱ; duration-∙ to duration-∙ʰⁱ)

-- a trace's floor measure is below its cap measure

durationˡᵒ≤ʰⁱ : (t : Trace) → durationˡᵒ t ≤ durationʰⁱ t
durationˡᵒ≤ʰⁱ = duration-mono costˡᵒ costʰⁱ cost-≤

------------------------------------------------------------------------
-- Coherence
--
-- `xs ◇ˢ ys` says some trace of `xs` takes no longer, at the floor's
-- cost model, than some trace of `ys` takes at the cap's. It is
-- decided, hence irrelevant.

infix 5 _◇ˢ₀_

_◇ˢ₀_ : List Trace → List Trace → Set
xs ◇ˢ₀ ys = True (any? (λ p → any? (λ q → durationˡᵒ p ≤? durationʰⁱ q) ys) xs)

◇ˢ₀-irr : {xs ys : List Trace} → (p q : xs ◇ˢ₀ ys) → p ≡ q
◇ˢ₀-irr {xs} {ys} =
  True-irr (any? (λ p → any? (λ q → durationˡᵒ p ≤? durationʰⁱ q) ys) xs)

-- against `unbounded` there is nothing to ask: an unbounded allowance
-- takes at least as long as any guarantee

infix 5 _◇ˢ_

_◇ˢ_ : List Trace → Bounds → Set
xs ◇ˢ (within Q) = xs ◇ˢ₀ tracesʰⁱ Q
xs ◇ˢ unbounded  = ⊤

◇ˢ-irr : {xs : List Trace} {Y : Bounds} → (p q : xs ◇ˢ Y) → p ≡ q
◇ˢ-irr {xs} {within Q}  = ◇ˢ₀-irr {xs} {tracesʰⁱ Q}
◇ˢ-irr {xs} {unbounded} tt tt = refl

-- a set is coherent with itself, at whichever member is to hand

◇ˢ₀-self : (xs : List Trace) → NonEmpty xs → xs ◇ˢ₀ xs
◇ˢ₀-self xs ne with neHead xs ne
... | t , t∈xs =
      fromWitness
        (Any.map (λ eq → subst (λ z → Any (λ q → durationˡᵒ z ≤ durationʰⁱ q)
                                            xs) eq inner) t∈xs)
  where
    inner : Any (λ q → durationˡᵒ t ≤ durationʰⁱ q) xs
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ t ≤ durationʰⁱ z) eq
                        (durationˡᵒ≤ʰⁱ t))
              t∈xs

-- and coherence survives the language product, durations adding along
-- sequencing

-- coherence only asks for one witnessing pair, so it travels along any
-- map that keeps the members -- normalisation in particular

◇ˢ₀-∈ : {xs xs' ys ys' : List Trace}
      → ({w : Trace} → w ∈ xs → w ∈ xs')
      → ({w : Trace} → w ∈ ys → w ∈ ys')
      → xs ◇ˢ₀ ys → xs' ◇ˢ₀ ys'
◇ˢ₀-∈ {xs} {xs'} {ys} {ys'} f g p
  with find (toWitness p)
... | t , t∈xs , hit
        with find hit
...     | s , s∈ys , t≤s =
          fromWitness
            (Any.map
              (λ eq → subst (λ z → Any (λ r → durationˡᵒ z ≤ durationʰⁱ r) ys')
                            eq inner)
              (f t∈xs))
  where
    inner : Any (λ r → durationˡᵒ t ≤ durationʰⁱ r) ys'
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ t ≤ durationʰⁱ z) eq t≤s) (g s∈ys)

-- reducing the floor keeps it: the witnessing guarantee is replaced by
-- one below it, which takes no longer

◇ˢ₀-nˡ : {xs ys : List Trace} → xs ◇ˢ₀ ys → nˡᵒ xs ◇ˢ₀ ys
◇ˢ₀-nˡ {xs} {ys} p
  with find (toWitness p)
... | t , t∈xs , hit
        with find hit
...     | s , s∈ys , t≤s
            with find (nˡᵒ-◃⁻ xs (◃ˡᵒ-∈ t∈xs))
...         | t' , t'∈n , t'≼t =
              fromWitness
                (Any.map
                  (λ eq → subst (λ z → Any (λ r → durationˡᵒ z ≤ durationʰⁱ r)
                                            ys) eq inner)
                  t'∈n)
  where
    inner : Any (λ r → durationˡᵒ t' ≤ durationʰⁱ r) ys
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ t' ≤ durationʰⁱ z) eq
                        (≤-trans (durᶠ t'≼t) t≤s))
              s∈ys

-- reducing the cap keeps it too: the witnessing allowance is replaced
-- by one above it, which takes no less

◇ˢ₀-nʰⁱ : {xs ys : List Trace} → xs ◇ˢ₀ ys → xs ◇ˢ₀ nʰⁱ ys
◇ˢ₀-nʰⁱ {xs} {ys} p
  with find (toWitness p)
... | t , t∈xs , hit
        with find hit
...     | s , s∈ys , t≤s
            with find (nʰⁱ-◃⁻ ys (◃ʰⁱ-∈ s∈ys))
...         | s' , s'∈n , s≼s' =
              fromWitness
                (Any.map
                  (λ eq → subst (λ z → Any (λ r → durationˡᵒ z ≤ durationʰⁱ r)
                                            (nʰⁱ ys)) eq inner)
                  t∈xs)
  where
    inner : Any (λ r → durationˡᵒ t ≤ durationʰⁱ r) (nʰⁱ ys)
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ t ≤ durationʰⁱ z) eq
                        (≤-trans t≤s (durᶜ s≼s')))
              s'∈n

-- both endpoints of a compound grade are reduced

◇ˢ₀-n-n : {xs ys : List Trace} → xs ◇ˢ₀ ys → nˡᵒ xs ◇ˢ₀ nʰⁱ ys
◇ˢ₀-n-n {xs} {ys} p = ◇ˢ₀-nʰⁱ {nˡᵒ xs} {ys} (◇ˢ₀-nˡ {xs} {ys} p)

◇ˢ₀-·ˢ : {xs xs' ys ys' : List Trace}
       → xs ◇ˢ₀ ys → xs' ◇ˢ₀ ys' → (xs ·ˢ xs') ◇ˢ₀ (ys ·ˢ ys')
◇ˢ₀-·ˢ {xs} {xs'} {ys} {ys'} p q
  with find (toWitness p)
... | t , t∈xs , hit
        with find hit
...     | s , s∈ys , t≤s
            with find (toWitness q)
...         | t' , t'∈xs' , hit'
                with find hit'
...             | s' , s'∈ys' , t'≤s' =
                  fromWitness
                    (Any.map
                      (λ eq → subst (λ z → Any (λ r → durationˡᵒ z ≤ durationʰⁱ r)
                                                (ys ·ˢ ys')) eq inner)
                      (∈-cartesianProductWith⁺ _∙_ t∈xs t'∈xs'))
  where
    bound : durationˡᵒ (t ∙ t') ≤ durationʰⁱ (s ∙ s')
    bound =
      ≤-trans (≤-reflexive (duration-∙ˡᵒ t t'))
              (≤-trans (+-mono-≤ t≤s t'≤s')
                       (≤-reflexive (sym (duration-∙ʰⁱ s s'))))

    inner : Any (λ r → durationˡᵒ (t ∙ t') ≤ durationʰⁱ r) (ys ·ˢ ys')
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ (t ∙ t') ≤ durationʰⁱ z) eq bound)
              (∈-cartesianProductWith⁺ _∙_ s∈ys s'∈ys')

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
  constructor [_,_,_]
  field
    lo : Antichain
    hi : Bounds
    -- some listed guarantee takes no longer than some listed allowance
    lo◇hi : tracesˡᵒ lo ◇ˢ hi

open TwoSided public

eqᵗˢ : {i₁ i₂ : TwoSided} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵗˢ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (◇ˢ-irr {tracesˡᵒ L} {U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵗˢ_

_·ᵗˢ_ : TwoSided → TwoSided → TwoSided
i₁ ·ᵗˢ i₂ =
  [ lo i₁ ·ˡᵒ lo i₂
  , hi i₁ ·ᵇ hi i₂
  , ◇ˢ-·ˢ {tracesˡᵒ (lo i₁)} {tracesˡᵒ (lo i₂)} {hi i₁} {hi i₂}
          (lo◇hi i₁) (lo◇hi i₂)
  ]

uᵗˢ : TwoSided
uᵗˢ = [ uˡᵒ , within uʰⁱ , ◇ˢ₀-self (tracesˡᵒ uˡᵒ) tt ]

-- the greatest grade: the weakest guarantee, which is the unit, under
-- an unbounded allowance

⊤ᵗˢ : TwoSided
⊤ᵗˢ = [ uˡᵒ , unbounded , tt ]

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
-- pair's own witnesses.

infixl 6 _⊔ᵗˢ_

_⊔ᵗˢ_ : TwoSided → TwoSided → TwoSided
i₁ ⊔ᵗˢ i₂ =
  [ lo i₁ ⊔ˡᵒ lo i₂
  , hi i₁ ⊔ᵇ hi i₂
  , ◇ˢ-⊔ᵇ {tracesˡᵒ (lo i₁)} {tracesˡᵒ (lo i₂)} {hi i₁} {hi i₂} (lo◇hi i₁)
  ]

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
-- Weakening replaces the witnessing guarantee by an easier one, which
-- takes no longer, and the witnessing allowance by a larger one, which
-- takes no less. So nothing the order reaches is refused by the field.

◇ˢ₀-≾ : (P : Antichain) (Q : Antichainʰⁱ) (L : Antichain) (U : Antichainʰⁱ)
      → tracesˡᵒ P ◇ˢ₀ tracesʰⁱ Q
      → P ≾ˡᵒ L → Q ≾ʰⁱ₀ U
      → tracesˡᵒ L ◇ˢ₀ tracesʰⁱ U
◇ˢ₀-≾ P Q L U coh l h
  with find (toWitness coh)
... | p , p∈L₁ , hit
        with find hit
...     | q , q∈U₁ , p≤q
            with find (toWitness (l p (fromWitness p∈L₁)))
...         | p' , p'∈L , p'≼p
                with find (toWitness (h q (fromWitness q∈U₁)))
...             | q' , q'∈U , q≼q' =
                  fromWitness
                    (Any.map
                      (λ eq → subst (λ z → Any (λ r → durationˡᵒ z ≤ durationʰⁱ r)
                                                (tracesʰⁱ U)) eq inner)
                      p'∈L)
  where
    inner : Any (λ r → durationˡᵒ p' ≤ durationʰⁱ r) (tracesʰⁱ U)
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ p' ≤ durationʰⁱ z) eq
                        (≤-trans (durᶠ p'≼p) (≤-trans p≤q (durᶜ q≼q'))))
              q'∈U

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

_≟ᵗˢ_ : Decidable (_≡_ {A = TwoSided})
i₁ ≟ᵗˢ i₂ with lo i₁ ≟ˡᵒ lo i₂ | hi i₁ ≟ᴮ hi i₂
... | yes p | yes q = yes (eqᵗˢ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers, and deciding the order

of-natᵗˢ : ℕ → TwoSided
of-natᵗˢ n =
  [ of-natˡᵒ n , within (of-natʰⁱ n) , ◇ˢ₀-self (tracesˡᵒ (of-natˡᵒ n)) tt ]

infix 5 _≾ᵗˢ?_

_≾ᵗˢ?_ : (i₁ i₂ : TwoSided) → Dec (i₁ ≾ᵗˢ i₂)
i₁ ≾ᵗˢ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of two-sided trace intervals

two-sided : Grade
two-sided = record
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
  ; ·-distribˡ-⊔    = ·ᵗˢ-distribˡ-⊔
  ; ·-distribʳ-⊔    = ·ᵗˢ-distribʳ-⊔
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵗˢ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵗˢ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗˢ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗˢ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵗˢ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗˢ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗˢ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵗˢ-irrelevant {c} {d}
  ; of-nat          = of-natᵗˢ
  ; of-nat-zero     = eqᵗˢ of-natˡᵒ-zero (cong within_ of-natʰⁱ-zero)
  ; of-nat-plus     = λ {m} {n} →
                        eqᵗˢ (of-natˡᵒ-plus {m} {n})
                             (cong within_ (of-natʰⁱ-plus {m} {n}))
  }
