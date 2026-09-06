------------------------------------------------------------------------
-- Lifting the sub-trace preorder to sets of timed traces.             --
--                                                                     --
-- Two lifts of `Traces.Subtrace`'s `_≼_`, which the trace-based grades --
-- pick their orders from:                                             --
--                                                                     --
--   xs ≼ˢ ys   every trace of `xs` fits inside some trace of `ys`     --
--   xs ≽ˢ ys   every trace of `ys` has some trace of `xs` inside it   --
--                                                                     --
-- Both are instances of `Sets.liftˢ`, the set-level lift of a decided  --
-- relation on traces: the Hoare lower lift is that scheme at `_≼_`,    --
-- and the Smyth upper lift is the same scheme at the *converse* `_≽_`, --
-- read backwards. It takes both of those dualities, not either alone:  --
-- swapping the two sets of `_≼ˢ_` leaves the witness above rather than --
-- below, so `xs ≽ˢ ys` and `ys ≼ˢ xs` are different relations and      --
-- neither implies the other.                                          --
--                                                                     --
-- Reflexivity, transitivity, monotonicity for the language product,    --
-- and decidability therefore come from `liftˢ`; what is proper to this --
-- module is how the two lifts sit against the unit `{ ε }`, which is   --
-- not symmetric between them.                                         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op cost
open import Syntax.Grades.Traces.SubtraceDuration Op cost using (≼-ε-inv)

open WithDecEq _≟ₒ_
  using (_∈?_; liftˢ; liftˢ-refl; liftˢ-trans; liftˢ-·ˢ; liftˢ?)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The converse sub-trace preorder
--
-- Naming it makes the Smyth lift an instance of the same scheme as the
-- Hoare one rather than a transcription of it.

infix 4 _≽_

_≽_ : Trace → Trace → Set
t ≽ s = s ≼ t

_≽?_ : Decidable _≽_
t ≽? s = s ≼? t

≽-trans : {s t u : Trace} → s ≽ t → t ≽ u → s ≽ u
≽-trans p q = ≼-trans q p

------------------------------------------------------------------------
-- The Hoare lower lift
--
-- The quantifier runs over the left-hand set: each of its traces is
-- witnessed to fit inside some trace of the right-hand one.

infix 5 _≼ˢ_

_≼ˢ_ : List Trace → List Trace → Set
_≼ˢ_ = liftˢ _≼_ _≼?_

≼ˢ-refl : {xs : List Trace} → xs ≼ˢ xs
≼ˢ-refl = liftˢ-refl _≼?_ ≼-refl

≼ˢ-trans : {xs ys zs : List Trace} → xs ≼ˢ ys → ys ≼ˢ zs → xs ≼ˢ zs
≼ˢ-trans = liftˢ-trans _≼?_ ≼-trans

-- the language product is monotone for the lift (in both arguments at
-- once), since the trace product is monotone for `_≼_`

≼ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ≼ˢ xs' → ys ≼ˢ ys' → (xs ·ˢ ys) ≼ˢ (xs' ·ˢ ys')
≼ˢ-·ˢ = liftˢ-·ˢ _≼?_ mono-∙

------------------------------------------------------------------------
-- The Smyth upper lift
--
-- Dual to `_≼ˢ_`: the quantifier runs over the *right-hand* set, and
-- the witness is found on the left. That is the Hoare lift of `_≽_`
-- with its two sets exchanged, so the three laws are the same three.

infix 5 _≽ˢ_

_≽ˢ_ : List Trace → List Trace → Set
xs ≽ˢ ys = liftˢ _≽_ _≽?_ ys xs

≽ˢ-refl : {xs : List Trace} → xs ≽ˢ xs
≽ˢ-refl = liftˢ-refl _≽?_ ≼-refl

≽ˢ-trans : {xs ys zs : List Trace} → xs ≽ˢ ys → ys ≽ˢ zs → xs ≽ˢ zs
≽ˢ-trans p q = liftˢ-trans _≽?_ ≽-trans q p

≽ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ≽ˢ xs' → ys ≽ˢ ys' → (xs ·ˢ ys) ≽ˢ (xs' ·ˢ ys')
≽ˢ-·ˢ = liftˢ-·ˢ _≽?_ mono-∙

------------------------------------------------------------------------
-- The unit is above everything for the Smyth lift
--
-- The empty trace fits inside every trace (`nil`), so `{ ε }` covers
-- any set from below. This is what makes `{ ε }` the *greatest* grade
-- in the orders built from `_≽ˢ_`, exactly as `[ 0 ,+∞⟩` is the
-- greatest left-sided interval.

u-≽ˢ : (xs : List Trace) → traces u ≽ˢ xs
u-≽ˢ xs s m = fromWitness {a? = any? (_≽?_ s) (traces u)} (here nil)

-- and, on a non-empty set, above everything for the Hoare lift too:
-- the empty trace fits inside whichever member is picked out

u-≼ˢ : (xs : List Trace) → NonEmpty xs → traces u ≼ˢ xs
u-≼ˢ xs ne s m
  with ∈-[ε]⁻ (toWitness {a? = s ∈? traces u} m)
... | refl
        with neHead xs ne
...     | t , t∈xs =
          fromWitness (Any.map (λ eq → subst (ε ≼_) eq nil) t∈xs)

------------------------------------------------------------------------
-- The unit is a zero for the Hoare lift
--
-- Unlike `_≽ˢ_`, the Hoare lift says something at the unit: `s ≼ ε`
-- forces `s` itself to be empty, since a spent run meets no demand but
-- the empty one. So if a language product lies below `{ ε }`, so does
-- each factor, the trace monoid being conical. This is the zero-product
-- property for any grade whose order caps by `_≼ˢ_`.

≼ˢ-zero-productˡ : {xs ys : List Trace} → NonEmpty ys
                 → (xs ·ˢ ys) ≼ˢ traces u → xs ≼ˢ traces u
≼ˢ-zero-productˡ {xs} {ys} ne hyp s m
  with neHead ys ne
... | y , y∈ys
        with find (toWitness (hyp (s ∙ y)
                     (fromWitness (∈-cartesianProductWith⁺ _∙_ (toWitness m) y∈ys))))
...     | t , t∈[ε] , sy≼t =
          fromWitness {a? = any? (_≼?_ s) (traces u)} (here s≼ε)
  where
    sy≼ε : (s ∙ y) ≼ ε
    sy≼ε = subst ((s ∙ y) ≼_) (∈-[ε]⁻ t∈[ε]) sy≼t

    s≼ε : s ≼ ε
    s≼ε = subst (_≼ ε) (sym (∙-conicalˡ {s} {y} (≼-ε-inv sy≼ε))) nil

≼ˢ-zero-productʳ : {xs ys : List Trace} → NonEmpty xs
                 → (xs ·ˢ ys) ≼ˢ traces u → ys ≼ˢ traces u
≼ˢ-zero-productʳ {xs} {ys} ne hyp s m
  with neHead xs ne
... | x , x∈xs
        with find (toWitness (hyp (x ∙ s)
                     (fromWitness (∈-cartesianProductWith⁺ _∙_ x∈xs (toWitness m)))))
...     | t , t∈[ε] , xs≼t =
          fromWitness {a? = any? (_≼?_ s) (traces u)} (here s≼ε)
  where
    xs≼ε : (x ∙ s) ≼ ε
    xs≼ε = subst ((x ∙ s) ≼_) (∈-[ε]⁻ t∈[ε]) xs≼t

    s≼ε : s ≼ ε
    s≼ε = subst (_≼ ε) (sym (∙-conicalʳ {x} {s} (≼-ε-inv xs≼ε))) nil

------------------------------------------------------------------------
-- Both lifts are decidable, being `liftˢ` at a decided relation

infix 5 _≼ˢ?_ _≽ˢ?_

_≼ˢ?_ : (xs ys : List Trace) → Dec (xs ≼ˢ ys)
_≼ˢ?_ = liftˢ? _≼?_

_≽ˢ?_ : (xs ys : List Trace) → Dec (xs ≽ˢ ys)
xs ≽ˢ? ys = liftˢ? _≽?_ ys xs
