------------------------------------------------------------------------
-- Lifting the sub-trace preorder to sets of timed traces.             --
--                                                                     --
-- Two lifts of `Traces.Subtrace`'s `_≼_`, which the trace-based grades --
-- pick their orders from:                                             --
--                                                                     --
--   xs ≼ˢ ys   every trace of `xs` fits inside some trace of `ys`     --
--   xs ≽ˢ ys   every trace of `ys` has some trace of `xs` inside it   --
--                                                                     --
-- Both are preorders and both are monotone for the language product,   --
-- since `_≼_` is a preorder monotone for the trace product. They       --
-- differ in which set the quantifier runs over, so neither implies     --
-- the other.                                                          --
--                                                                     --
-- Membership and `_≼_` are both decided, so the lifts are stated in    --
-- the proof-irrelevant `True`-of-a-decision form.                      --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceLift
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.Subtrace Op cost

open WithDecEq _≟ₒ_ using (_∈?_)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The Hoare lower lift
--
-- The quantifier runs over the left-hand set: each of its traces is
-- witnessed to fit inside some trace of the right-hand one.

infix 5 _≼ˢ_

_≼ˢ_ : List Trace → List Trace → Set
xs ≼ˢ ys = (s : Trace) → True (s ∈? xs) → True (any? (λ t → s ≼? t) ys)

≼ˢ-refl : {xs : List Trace} → xs ≼ˢ xs
≼ˢ-refl {xs} s m =
  fromWitness (Any.map (λ eq → subst (s ≼_) eq (≼-refl s)) (toWitness m))

≼ˢ-trans : {xs ys zs : List Trace} → xs ≼ˢ ys → ys ≼ˢ zs → xs ≼ˢ zs
≼ˢ-trans {xs} {ys} {zs} xy yz s m
  with find (toWitness (xy s m))
... | y , y∈ys , s≼y
        with find (toWitness (yz y (fromWitness y∈ys)))
...     | z , z∈zs , y≼z =
          fromWitness
            (Any.map (λ eq → subst (s ≼_) eq (≼-trans s≼y y≼z)) z∈zs)

-- the language product is monotone for the lift (in both arguments at
-- once), since the trace product is monotone for `_≼_`

≼ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ≼ˢ xs' → ys ≼ˢ ys' → (xs ·ˢ ys) ≼ˢ (xs' ·ˢ ys')
≼ˢ-·ˢ {xs} {xs'} {ys} {ys'} pxs pys r m
  with ∈-cartesianProductWith⁻ _∙_ xs ys (toWitness m)
... | a , b , a∈xs , b∈ys , refl
        with find (toWitness (pxs a (fromWitness a∈xs)))
           | find (toWitness (pys b (fromWitness b∈ys)))
...     | a' , a'∈ , a≼a' | b' , b'∈ , b≼b' =
          fromWitness
            (Any.map (λ eq → subst ((a ∙ b) ≼_) eq (mono-∙ a≼a' b≼b'))
                     (∈-cartesianProductWith⁺ _∙_ a'∈ b'∈))

------------------------------------------------------------------------
-- The Smyth upper lift
--
-- Dual to `_≼ˢ_`: the quantifier runs over the *right-hand* set, and
-- the witness is found on the left.

infix 5 _≽ˢ_

_≽ˢ_ : List Trace → List Trace → Set
xs ≽ˢ ys = (t : Trace) → True (t ∈? ys) → True (any? (λ s → s ≼? t) xs)

≽ˢ-refl : {xs : List Trace} → xs ≽ˢ xs
≽ˢ-refl {xs} t m =
  fromWitness (Any.map (λ eq → subst (_≼ t) eq (≼-refl t)) (toWitness m))

≽ˢ-trans : {xs ys zs : List Trace} → xs ≽ˢ ys → ys ≽ˢ zs → xs ≽ˢ zs
≽ˢ-trans {xs} {ys} {zs} xy yz t m
  with find (toWitness (yz t m))
... | y , y∈ys , y≼t
        with find (toWitness (xy y (fromWitness y∈ys)))
...     | x , x∈xs , x≼y =
          fromWitness
            (Any.map (λ eq → subst (_≼ t) eq (≼-trans x≼y y≼t)) x∈xs)

≽ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ≽ˢ xs' → ys ≽ˢ ys' → (xs ·ˢ ys) ≽ˢ (xs' ·ˢ ys')
≽ˢ-·ˢ {xs} {xs'} {ys} {ys'} pxs pys r m
  with ∈-cartesianProductWith⁻ _∙_ xs' ys' (toWitness m)
... | a' , b' , a'∈xs' , b'∈ys' , refl
        with find (toWitness (pxs a' (fromWitness a'∈xs')))
           | find (toWitness (pys b' (fromWitness b'∈ys')))
...     | a , a∈xs , a≼a' | b , b∈ys , b≼b' =
          fromWitness
            (Any.map (λ eq → subst (_≼ (a' ∙ b')) eq (mono-∙ a≼a' b≼b'))
                     (∈-cartesianProductWith⁺ _∙_ a∈xs b∈ys))

------------------------------------------------------------------------
-- The unit is above everything for the Smyth lift
--
-- The empty trace fits inside every trace (`nil`), so `{ ε }` covers
-- any set from below. This is what makes `{ ε }` the *greatest* grade
-- in the orders built from `_≽ˢ_`, exactly as `[ 0 ,+∞⟩` is the
-- greatest left-sided interval.

u-≽ˢ : (xs : List Trace) → traces u ≽ˢ xs
u-≽ˢ xs t m = fromWitness {a? = any? (λ s → s ≼? t) (traces u)} (here nil)

-- and, on a non-empty set, above everything for the Hoare lift too:
-- the empty trace fits inside whichever member is picked out

u-≼ˢ : (xs : List Trace) → NonEmpty xs → traces u ≼ˢ xs
u-≼ˢ xs ne s m
  with ∈-[ε]⁻ (toWitness {a? = s ∈? traces u} m)
... | refl
        with neHead xs ne
...     | t , t∈xs =
          fromWitness (Any.map (λ eq → subst (ε ≼_) eq nil) t∈xs)
