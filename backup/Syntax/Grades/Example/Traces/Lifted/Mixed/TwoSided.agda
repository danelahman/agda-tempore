------------------------------------------------------------------------
-- Two-sided trace intervals with a Smyth floor and a Hoare cap.       --
--                                                                     --
-- The one cell of the grid whose two endpoints are lifted differently, --
-- and the one that bounds a computation the way a time interval does.  --
-- Read a grade against the set `X` of runs a computation may have:     --
--                                                                     --
--   floor   every run of `X` covers some demand of `L`                --
--   cap     every run of `X` stays within some allowance of `U`       --
--                                                                     --
-- Both are statements about *every* run, which is what `min ≤ t ≤ max` --
-- says of a duration, and neither of the pure columns says: `LowerLift --
-- .TwoSided` reads its floor as "some run covers each listed demand",  --
-- and `UpperLift.TwoSided` reads its cap as "each listed allowance is  --
-- realised by some run". So this is the pairing to reach for when the  --
-- endpoints are meant to bound each run from opposite sides.           --
--                                                                     --
-- The two conditions are one half of the Egli-Milner order apiece --   --
-- the Smyth half at the floor, the Hoare half at the cap -- and they   --
-- force the orders on the endpoints:                                   --
--                                                                     --
--   [ L₁ , U₁ ] ≾ [ L₂ , U₂ ]   iff   L₂ ≽ˢ L₁   and   U₁ ≼ˢ U₂      --
--                                                                     --
-- that is, every trace of `L₁` has one of `L₂` below it and every      --
-- trace of `U₁` has one of `U₂` above it. Taking `X := L₁` and         --
-- `X := U₁` shows each half necessary, and transitivity of the lifts   --
-- shows it sufficient. Weakening therefore *adds* members at either    --
-- endpoint: both sets are read disjunctively -- meet one listed        --
-- demand, stay within one listed allowance -- so a longer list asks    --
-- for less at both ends.                                              --
--                                                                     --
-- Order-theoretically, each endpoint is a finite set of generators,    --
-- compared by inclusion of the set of runs it generates. Writing       --
-- `↑L = { x | l ≼ x for some l ∈ L }` for the runs meeting a floor and --
-- `↓U = { x | x ≼ u for some u ∈ U }` for those within a cap,          --
--                                                                     --
--   L₁ ≾ L₂  iff  ↑L₁ ⊆ ↑L₂        U₁ ≾ U₂  iff  ↓U₁ ⊆ ↓U₂           --
--                                                                     --
-- so each endpoint is a finitely generated up-set, resp. down-set,     --
-- ordered by inclusion, and union is the join at both. That is the     --
-- shape a branching construct would need, and it is also the sense in  --
-- which a grade denotes the interval `↑L ∩ ↓U` of runs it admits.      --
--                                                                     --
-- Named, each endpoint is the finitary disjunctive completion of the   --
-- trace order -- the free join-semilattice on it, a finite set of      --
-- generators denoting the join of what its members denote -- taken     --
-- over `_≽_` below and over `_≼_` above. "Disjunctive" is a claim      --
-- about the *set*: its members are combined by `∨`. The quantifier     --
-- over the runs is universal at both endpoints, so neither is a "may"  --
-- reading in the powerdomain sense, Hoare-shaped though both lifts     --
-- are.                                                                 --
--                                                                     --
-- The quantifiers of both conditions are written out at the carrier    --
-- below. Both halves of the order run universally over the *source*    --
-- grade's set and existentially over the target's; all that differs    --
-- between them is which way `_≼_` points. Neither exchanges its sets - --
-- it is one `Sets.liftˢ` in one argument order, at `_≽_` below and at  --
-- `_≼_` above, `UpperLift.LeftSided`'s exchange cancelling the one     --
-- inside `_≽ˢ_` -- which `floor-lift` and `cap-lift` below check.      --
--                                                                     --
-- The four one-sided grades are the four ways of fixing those two      --
-- axes, and the remaining two quantify universally over the *target*:  --
--                                                                     --
--   ∀ q ∈ Q. ∃ p ∈ P. q ≼ p     LowerLift.LeftSided                   --
--   ∀ q ∈ Q. ∃ p ∈ P. p ≼ q     UpperLift.RightSided                  --
--                                                                     --
-- A set is read disjunctively exactly when it is the existential one   --
-- while it is the weaker grade: a further alternative can then only    --
-- help. That is this row of the square; in the other row the weaker    --
-- grade's set is quantified universally, and an extra member there is  --
-- a further demand.                                                    --
--                                                                     --
-- The consistency field is the existential `_◇ˢ_`: some demand of the  --
-- floor fits inside some allowance of the cap. That is exactly         --
-- inhabitation -- a run `l ≼ x ≼ u` exists iff `l ≼ u` does -- and it  --
-- is the only one of the three candidates the order preserves. Asking  --
-- `L ≼ˢ U` (`LowerLift.TwoSided`'s field) would refuse a floor whose   --
-- extra demand no allowance covers, and asking `L ≽ˢ U`               --
-- (`UpperLift.TwoSided`'s) would refuse a cap whose extra allowance    --
-- covers no demand -- and adding such a member at either endpoint is a --
-- legitimate weakening here. `Worked.Traces.Subtrace.Mixed` decides    --
-- both of those, and `◇ˢ-≾` below is the closure this one does have.   --
--                                                                     --
-- The order lifted is a parameter: `Traces.Subtrace`'s lenient one and --
-- `Traces.SubtraceTimed`'s time-strict one both instantiate it, under  --
-- `Example.Traces.Subtrace` and `Example.Traces.SubtraceTimed`.        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.Mixed.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Data.List.Base using (List)
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
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

-- the floor is ordered as the Smyth-lift one-sided grade orders it,
-- the cap as the Hoare-lift one -- the two halves this cell mixes

open import Syntax.Grades.Example.Traces.Lifted.UpperLift.LeftSided Op _≟ₒ_ O
  using () renaming (_≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_;
                     ≾ᵗ-zero-productˡ to ≾ˡᵒ-zero-productˡ;
                     ≾ᵗ-zero-productʳ to ≾ˡᵒ-zero-productʳ)
open import Syntax.Grades.Example.Traces.Lifted.LowerLift.RightSided Op _≟ₒ_ O
  using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_;
                     ≾ᵗ-zero-productˡ to ≾ʰⁱ-zero-productˡ;
                     ≾ᵗ-zero-productʳ to ≾ʰⁱ-zero-productʳ)

open Order.TraceOrder O
open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ; liftˢ-irrelevant; True-irr)

------------------------------------------------------------------------
-- Consistency
--
-- `xs ◇ˢ ys` says some member of `xs` fits inside some member of `ys`.
-- Both quantifiers are existential, which is what separates it from
-- either lift, and it is decided, hence irrelevant.

infix 5 _◇ˢ_

_◇ˢ_ : List Trace → List Trace → Set
xs ◇ˢ ys = True (any? (λ t → any? (t ≼?_) ys) xs)

◇ˢ-irr : {xs ys : List Trace} → (p q : xs ◇ˢ ys) → p ≡ q
◇ˢ-irr {xs} {ys} = True-irr (any? (λ t → any? (t ≼?_) ys) xs)

-- a set is consistent with itself, at whichever member is to hand

◇ˢ-refl : (P : NeTraces) → traces P ◇ˢ traces P
◇ˢ-refl P with neHead (traces P) (nonempty P)
... | t , t∈P =
      fromWitness
        (Any.map (λ eq → subst (λ z → Any (z ≼_) (traces P)) eq inner) t∈P)
  where
    inner : Any (t ≼_) (traces P)
    inner = Any.map (λ eq → subst (t ≼_) eq (≼-refl t)) t∈P

-- and consistency survives the language product, the trace product
-- being monotone

◇ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ◇ˢ ys → xs' ◇ˢ ys' → (xs ·ˢ xs') ◇ˢ (ys ·ˢ ys')
◇ˢ-·ˢ {xs} {xs'} {ys} {ys'} p q
  with find (toWitness p)
... | t , t∈xs , hit
        with find hit
...     | s , s∈ys , t≼s
            with find (toWitness q)
...         | t' , t'∈xs' , hit'
                with find hit'
...             | s' , s'∈ys' , t'≼s' =
                  fromWitness
                    (Any.map
                      (λ eq → subst (λ z → Any (z ≼_) (ys ·ˢ ys')) eq inner)
                      (∈-cartesianProductWith⁺ _∙_ t∈xs t'∈xs'))
  where
    inner : Any ((t ∙ t') ≼_) (ys ·ˢ ys')
    inner =
      Any.map (λ eq → subst ((t ∙ t') ≼_) eq (mono-∙ t≼s t'≼s'))
              (∈-cartesianProductWith⁺ _∙_ s∈ys s'∈ys')

------------------------------------------------------------------------
-- The carrier
--
-- A floor and a cap, each bounding every run. Writing `X` for the set
-- of runs a computation may have, and reading `l ≼ x` as "the run `x`
-- does at least what `l` asks for", the grade `[ L , U ]` is the pair
-- of conditions
--
--   ∀ x ∈ X. ∃ l ∈ L. l ≼ x      every run covers some listed demand
--   ∀ x ∈ X. ∃ u ∈ U. x ≼ u      every run stays within some allowance
--
-- and the order weakening them is, half for half,
--
--   [ L₁ , U₁ ] ≾ [ L₂ , U₂ ]  =  (∀ l ∈ L₁. ∃ l' ∈ L₂. l' ≼ l)
--                              ×  (∀ u ∈ U₁. ∃ u' ∈ U₂. u  ≼ u')
--
-- universal over the source grade's set and existential over the
-- target's at both endpoints, the two halves differing only in which
-- way `_≼_` points. Equivalently, and this is `floor-lift`/`cap-lift`
-- below, each half is `Sets.liftˢ` in the argument order written -- at
-- `_≽_` for the floor and at `_≼_` for the cap.

record MixedInterval : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- some demand of the floor fits inside some allowance of the cap,
    -- so a run meeting the floor without leaving the cap exists
    lo◇hi : traces lo ◇ˢ traces hi

open MixedInterval public

-- two intervals are equal as soon as their endpoints are: the
-- consistency witness is a `True`-of-a-decision, hence irrelevant

eqᵐⁱ : {i₁ i₂ : MixedInterval} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵐⁱ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (◇ˢ-irr {traces L} {traces U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵐⁱ_

_·ᵐⁱ_ : MixedInterval → MixedInterval → MixedInterval
i₁ ·ᵐⁱ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ◇ˢ-·ˢ {traces (lo i₁)} {traces (lo i₂)} {traces (hi i₁)} {traces (hi i₂)}
          (lo◇hi i₁) (lo◇hi i₂)
  ]

uᵐⁱ : MixedInterval
uᵐⁱ = [ u , u , ◇ˢ-refl u ]

·ᵐⁱ-identityʳ : (i : MixedInterval) → (i ·ᵐⁱ uᵐⁱ) ≡ i
·ᵐⁱ-identityʳ i = eqᵐⁱ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ᵐⁱ-identityˡ : (i : MixedInterval) → (uᵐⁱ ·ᵐⁱ i) ≡ i
·ᵐⁱ-identityˡ i = eqᵐⁱ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ᵐⁱ-assoc : (i₁ i₂ i₃ : MixedInterval)
          → ((i₁ ·ᵐⁱ i₂) ·ᵐⁱ i₃) ≡ (i₁ ·ᵐⁱ (i₂ ·ᵐⁱ i₃))
·ᵐⁱ-assoc i₁ i₂ i₃ =
  eqᵐⁱ (·-assoc (lo i₁) (lo i₂) (lo i₃))
       (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: the floor drops, the cap rises, each at its own lift

infix 5 _≾ᵐⁱ_

_≾ᵐⁱ_ : MixedInterval → MixedInterval → Set
i₁ ≾ᵐⁱ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

-- and both halves are one scheme in one argument order, the relation
-- being all that differs: neither endpoint exchanges its two sets, so
-- the quantifier runs over the source set at both

floor-lift : (P Q : NeTraces)
           → (P ≾ˡᵒ Q) ≡ liftˢ _≽_ _≽?_ (traces P) (traces Q)
floor-lift _ _ = refl

cap-lift : (P Q : NeTraces)
         → (P ≾ʰⁱ Q) ≡ liftˢ _≼_ _≼?_ (traces P) (traces Q)
cap-lift _ _ = refl

≾ᵐⁱ-refl : {i : MixedInterval} → i ≾ᵐⁱ i
≾ᵐⁱ-refl {i} = ≽ˢ-refl {traces (lo i)} , ≼ˢ-refl {traces (hi i)}

≾ᵐⁱ-trans : {i₁ i₂ i₃ : MixedInterval} → i₁ ≾ᵐⁱ i₂ → i₂ ≾ᵐⁱ i₃ → i₁ ≾ᵐⁱ i₃
≾ᵐⁱ-trans {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ≽ˢ-trans {traces (lo i₃)} {traces (lo i₂)} {traces (lo i₁)} l₂ l₁
  , ≼ˢ-trans {traces (hi i₁)} {traces (hi i₂)} {traces (hi i₃)} h₁ h₂

-- the product is monotone endpoint by endpoint

·ᵐⁱ-monoˡ : {c i₁ i₂ : MixedInterval} → i₁ ≾ᵐⁱ i₂ → (i₁ ·ᵐⁱ c) ≾ᵐⁱ (i₂ ·ᵐⁱ c)
·ᵐⁱ-monoˡ {c} {i₁} {i₂} (l , h) =
    ≽ˢ-·ˢ {traces (lo i₂)} {traces (lo i₁)} {traces (lo c)} {traces (lo c)}
          l (≽ˢ-refl {traces (lo c)})
  , ≼ˢ-·ˢ {traces (hi i₁)} {traces (hi i₂)} {traces (hi c)} {traces (hi c)}
          h (≼ˢ-refl {traces (hi c)})

·ᵐⁱ-monoʳ : {c i₁ i₂ : MixedInterval} → i₁ ≾ᵐⁱ i₂ → (c ·ᵐⁱ i₁) ≾ᵐⁱ (c ·ᵐⁱ i₂)
·ᵐⁱ-monoʳ {c} {i₁} {i₂} (l , h) =
    ≽ˢ-·ˢ {traces (lo c)} {traces (lo c)} {traces (lo i₂)} {traces (lo i₁)}
          (≽ˢ-refl {traces (lo c)}) l
  , ≼ˢ-·ˢ {traces (hi c)} {traces (hi c)} {traces (hi i₁)} {traces (hi i₂)}
          (≼ˢ-refl {traces (hi c)}) h

------------------------------------------------------------------------
-- The consistency field travels along the order
--
-- Weakening replaces the witnessing demand by one below it and the
-- witnessing allowance by one above it, so the pair `l ≼ u` becomes
-- `l' ≼ l ≼ u ≼ u'`. Nothing the order allows is therefore blocked by
-- the field -- which is what recommends this field over the two lifted
-- ones, neither of which is closed this way.

◇ˢ-≾ : (i₁ : MixedInterval) (L U : NeTraces)
     → lo i₁ ≾ˡᵒ L → hi i₁ ≾ʰⁱ U
     → traces L ◇ˢ traces U
◇ˢ-≾ i₁ L U l h
  with find (toWitness (lo◇hi i₁))
... | t , t∈L₁ , hit
        with find hit
...     | s , s∈U₁ , t≼s
            with find (toWitness (l t (fromWitness t∈L₁)))
...         | t' , t'∈L , t'≼t
                with find (toWitness (h s (fromWitness s∈U₁)))
...             | s' , s'∈U , s≼s' =
                  fromWitness
                    (Any.map
                      (λ eq → subst (λ z → Any (z ≼_) (traces U)) eq inner)
                      t'∈L)
  where
    inner : Any (t' ≼_) (traces U)
    inner =
      Any.map (λ eq → subst (t' ≼_) eq
                        (≼-trans t'≼t (≼-trans t≼s s≼s')))
              s'∈U

-- so the weakened pair really is a grade

weaken : (i : MixedInterval) (L U : NeTraces)
       → lo i ≾ˡᵒ L → hi i ≾ʰⁱ U
       → MixedInterval
weaken i L U l h = [ L , U , ◇ˢ-≾ i L U l h ]

weaken-≾ : (i : MixedInterval) (L U : NeTraces)
         → (l : lo i ≾ˡᵒ L) → (h : hi i ≾ʰⁱ U)
         → i ≾ᵐⁱ weaken i L U l h
weaken-≾ i L U l h = l , h

------------------------------------------------------------------------
-- Zero-product property
--
-- Only the cap carries information at the unit, as in the pure Hoare
-- pair: `[ L , U ] ≾ uᵐⁱ` asks every trace of `U` to take no time, and
-- durations add along sequencing. The floor half is vacuous, `{ ε }`
-- being the greatest Smyth floor.

≾ᵐⁱ-zero-productˡ : {i₁ i₂ : MixedInterval} → (i₁ ·ᵐⁱ i₂) ≾ᵐⁱ uᵐⁱ → i₁ ≾ᵐⁱ uᵐⁱ
≾ᵐⁱ-zero-productˡ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productˡ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productˡ {hi i₁} {hi i₂} h

≾ᵐⁱ-zero-productʳ : {i₁ i₂ : MixedInterval} → (i₁ ·ᵐⁱ i₂) ≾ᵐⁱ uᵐⁱ → i₂ ≾ᵐⁱ uᵐⁱ
≾ᵐⁱ-zero-productʳ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productʳ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productʳ {hi i₁} {hi i₂} h

-- both halves are decided, so the order is proof-irrelevant

≾ᵐⁱ-irrelevant : {i₁ i₂ : MixedInterval} → (p q : i₁ ≾ᵐⁱ i₂) → p ≡ q
≾ᵐⁱ-irrelevant {i₁} {i₂} (l , h) (l' , h') =
  cong₂ _,_ (liftˢ-irrelevant l l') (liftˢ-irrelevant h h')

-- decidable equality, endpoint by endpoint

_≟ᵐⁱ_ : Decidable (_≡_ {A = MixedInterval})
i₁ ≟ᵐⁱ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᵐⁱ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers
--
-- `n` time steps is the pure delay `⟨ n ⟩` at both endpoints: every run
-- takes at least that long and no longer.

of-natᵐⁱ : ℕ → MixedInterval
of-natᵐⁱ n = [ of-nat n , of-nat n , ◇ˢ-refl (of-nat n) ]

------------------------------------------------------------------------
-- The order is decidable, endpoint by endpoint

infix 5 _≾ᵐⁱ?_

_≾ᵐⁱ?_ : (i₁ i₂ : MixedInterval) → Dec (i₁ ≾ᵐⁱ i₂)
i₁ ≾ᵐⁱ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of mixed two-sided trace intervals

mixed-two-sided : Grade
mixed-two-sided = record
  { Carrier         = MixedInterval
  ; _·_             = _·ᵐⁱ_
  ; u               = uᵐⁱ
  ; ·-identityʳ     = ·ᵐⁱ-identityʳ
  ; ·-identityˡ     = ·ᵐⁱ-identityˡ
  ; ·-assoc         = ·ᵐⁱ-assoc
  ; _≾_             = _≾ᵐⁱ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵐⁱ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵐⁱ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵐⁱ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵐⁱ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵐⁱ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵐⁱ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵐⁱ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵐⁱ-irrelevant {c} {d}
  ; of-nat          = of-natᵐⁱ
  ; of-nat-zero     = eqᵐⁱ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqᵐⁱ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }

