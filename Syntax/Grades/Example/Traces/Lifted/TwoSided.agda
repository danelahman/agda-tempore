------------------------------------------------------------------------
-- Sets of timed traces bounding a computation from both sides.        --
--                                                                     --
-- A grade is a pair `[ P , Q ]` of non-empty finite sets of traces,    --
-- read against the runs `X` a computation may have:                    --
--                                                                     --
--   ∀ x ∈ X. ∃ p ∈ P. p ≼ᶠ x     whatever happened, at least one of   --
--                                the listed guarantees was covered     --
--   ∀ x ∈ X. ∃ q ∈ Q. x ≼ᶜ q     and it stayed within one of the      --
--                                listed allowances                    --
--                                                                     --
-- Both halves are universal over the runs and existential over the     --
-- set, so both endpoints are read disjunctively, both weaken by        --
-- gaining members, and the union of two grades is their join at either --
-- end -- the shape a branching construct wants.                        --
--                                                                     --
-- The two endpoints take *different* orders, and must. A guarantee     --
-- wants an order in which time never buys an operation, and an         --
-- allowance one in which a listed delay is a budget that buys them; a  --
-- single order cannot do both. So the construction takes `Oᶠ` and `Oᶜ` --
-- separately, and `Example.Traces.Timed.TwoSided` instantiates them at --
-- `Traces.Coverage` and `Traces.Allowance`. Those two are              --
-- incomparable -- neither contains the other -- which is what the      --
-- coherence field below has to work around.                            --
--                                                                     --
-- The field asks that some listed guarantee take no longer than some   --
-- listed allowance. That is *necessary* for the grade to admit any run --
-- at all, since a run covering `p` and staying within `q` has          --
-- `durationˡᵒ p ≤ duration x ≤ durationʰⁱ q`, so no admissible grade   --
-- is refused; and it is what downstream needs, being exactly           --
-- `min ≤ max` for the projection to time intervals. A sufficient       --
-- condition would have to relate the two orders, and with incomparable --
-- orders any such condition refuses grades the order itself reaches -- --
-- the trap a coherence field stated in one of the two lifts falls      --
-- into.                                                                --
--                                                                     --
-- The two endpoints also take *different* cost models, and must. An    --
-- operation's execution time is only known to lie in a range, and a    --
-- guarantee may credit it with no more than its least (`costˡᵒ`) while --
-- an allowance must budget for its greatest (`costʰⁱ`). The field      --
-- straddles the two, so it needs `cost-≤` to compare them at all.      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _≤_)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Base as Base
import Syntax.Grades.Traces.Durations as Dur
import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op)
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

open import Data.List.Base using (List)
open import Data.Nat using (_+_; _≤?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤)
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Durations Op

-- each endpoint is ordered exactly as the corresponding one-sided grade
-- orders it, at its own order

open import Syntax.Grades.Example.Traces.Lifted.LeftSided Op _≟ₒ_ Oᶠ
  using () renaming (_≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_;
                     ≾-refl to ≾ˡᵒ-refl; ≾-trans to ≾ˡᵒ-trans;
                     ·-monoˡ to ·ˡᵒ-monoˡ; ·-monoʳ to ·ˡᵒ-monoʳ;
                     ≾-zero-productˡ to ≾ˡᵒ-zero-productˡ;
                     ≾-zero-productʳ to ≾ˡᵒ-zero-productʳ;
                     ≾-irrelevant to ≾ˡᵒ-irrelevant)
open import Syntax.Grades.Example.Traces.Lifted.RightSided Op _≟ₒ_ Oᶜ
  using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_;
                     ≾-refl to ≾ʰⁱ-refl; ≾-trans to ≾ʰⁱ-trans;
                     ·-monoˡ to ·ʰⁱ-monoˡ; ·-monoʳ to ·ʰⁱ-monoʳ;
                     ≾-zero-productˡ to ≾ʰⁱ-zero-productˡ;
                     ≾-zero-productʳ to ≾ʰⁱ-zero-productʳ;
                     ≾-irrelevant to ≾ʰⁱ-irrelevant)

-- each endpoint is measured at its own cost model

open Durations costˡᵒ using ()
  renaming (duration to durationˡᵒ; duration-∙ to duration-∙ˡᵒ)
open Durations costʰⁱ using ()
  renaming (duration to durationʰⁱ; duration-∙ to duration-∙ʰⁱ)

open WithDecEq _≟ₒ_ using (_≟ᴺ_; True-irr)

-- a trace's floor measure is below its cap measure

durationˡᵒ≤ʰⁱ : (t : Trace) → durationˡᵒ t ≤ durationʰⁱ t
durationˡᵒ≤ʰⁱ = duration-mono costˡᵒ costʰⁱ cost-≤

------------------------------------------------------------------------
-- Coherence
--
-- `xs ◇ˢ ys` says some trace of `xs` takes no longer, at the floor's
-- cost model, than some trace of `ys` takes at the cap's. It is
-- decided, hence irrelevant.

infix 5 _◇ˢ_

_◇ˢ_ : List Trace → List Trace → Set
xs ◇ˢ ys = True (any? (λ p → any? (λ q → durationˡᵒ p ≤? durationʰⁱ q) ys) xs)

◇ˢ-irr : {xs ys : List Trace} → (p q : xs ◇ˢ ys) → p ≡ q
◇ˢ-irr {xs} {ys} =
  True-irr (any? (λ p → any? (λ q → durationˡᵒ p ≤? durationʰⁱ q) ys) xs)

-- a set is coherent with itself, at whichever member is to hand

◇ˢ-refl : (P : NeTraces) → traces P ◇ˢ traces P
◇ˢ-refl P with neHead (traces P) (nonempty P)
... | t , t∈P =
      fromWitness
        (Any.map (λ eq → subst (λ z → Any (λ q → durationˡᵒ z ≤ durationʰⁱ q)
                                            (traces P)) eq inner) t∈P)
  where
    inner : Any (λ q → durationˡᵒ t ≤ durationʰⁱ q) (traces P)
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ t ≤ durationʰⁱ z) eq
                        (durationˡᵒ≤ʰⁱ t))
              t∈P

-- and coherence survives the language product, durations adding along
-- sequencing

◇ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ◇ˢ ys → xs' ◇ˢ ys' → (xs ·ˢ xs') ◇ˢ (ys ·ˢ ys')
◇ˢ-·ˢ {xs} {xs'} {ys} {ys'} p q
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

------------------------------------------------------------------------
-- The carrier

record TwoSided : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- some listed guarantee takes no longer than some listed allowance
    lo◇hi : traces lo ◇ˢ traces hi

open TwoSided public

eqᵗˢ : {i₁ i₂ : TwoSided} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵗˢ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (◇ˢ-irr {traces L} {traces U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵗˢ_

_·ᵗˢ_ : TwoSided → TwoSided → TwoSided
i₁ ·ᵗˢ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ◇ˢ-·ˢ {traces (lo i₁)} {traces (lo i₂)} {traces (hi i₁)} {traces (hi i₂)}
          (lo◇hi i₁) (lo◇hi i₂)
  ]

uᵗˢ : TwoSided
uᵗˢ = [ u , u , ◇ˢ-refl u ]

·ᵗˢ-identityʳ : (i : TwoSided) → (i ·ᵗˢ uᵗˢ) ≡ i
·ᵗˢ-identityʳ i = eqᵗˢ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ᵗˢ-identityˡ : (i : TwoSided) → (uᵗˢ ·ᵗˢ i) ≡ i
·ᵗˢ-identityˡ i = eqᵗˢ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ᵗˢ-assoc : (i₁ i₂ i₃ : TwoSided)
          → ((i₁ ·ᵗˢ i₂) ·ᵗˢ i₃) ≡ (i₁ ·ᵗˢ (i₂ ·ᵗˢ i₃))
·ᵗˢ-assoc i₁ i₂ i₃ =
  eqᵗˢ (·-assoc (lo i₁) (lo i₂) (lo i₃))
       (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: each endpoint at its own order

infix 5 _≾ᵗˢ_

_≾ᵗˢ_ : TwoSided → TwoSided → Set
i₁ ≾ᵗˢ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

≾ᵗˢ-refl : {i : TwoSided} → i ≾ᵗˢ i
≾ᵗˢ-refl {i} = ≾ˡᵒ-refl {lo i} , ≾ʰⁱ-refl {hi i}

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
-- The coherence field travels along the order
--
-- Weakening replaces the witnessing guarantee by an easier one, which
-- takes no longer, and the witnessing allowance by a larger one, which
-- takes no less. So nothing the order reaches is refused by the field.

◇ˢ-≾ : (i : TwoSided) (L U : NeTraces)
     → lo i ≾ˡᵒ L → hi i ≾ʰⁱ U
     → traces L ◇ˢ traces U
◇ˢ-≾ i L U l h
  with find (toWitness (lo◇hi i))
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
                                                (traces U)) eq inner)
                      p'∈L)
  where
    inner : Any (λ r → durationˡᵒ p' ≤ durationʰⁱ r) (traces U)
    inner =
      Any.map (λ eq → subst (λ z → durationˡᵒ p' ≤ durationʰⁱ z) eq
                        (≤-trans (durᶠ p'≼p) (≤-trans p≤q (durᶜ q≼q'))))
              q'∈U

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
i₁ ≟ᵗˢ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᵗˢ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers, and deciding the order

of-natᵗˢ : ℕ → TwoSided
of-natᵗˢ n = [ of-nat n , of-nat n , ◇ˢ-refl (of-nat n) ]

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
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵗˢ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵗˢ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗˢ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗˢ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵗˢ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗˢ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗˢ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵗˢ-irrelevant {c} {d}
  ; of-nat          = of-natᵗˢ
  ; of-nat-zero     = eqᵗˢ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqᵗˢ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }
