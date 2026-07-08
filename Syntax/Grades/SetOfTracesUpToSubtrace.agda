-----------------------------------------------------------------
-- Sets of timed traces, ordered up to the sub-trace preorder: --
--                                                             --
--   P ≾ Q   iff   every trace of P is `≼` some trace of Q.    --
--                                                             --
-----------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.SetOfTracesUpToSubtrace
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades

-- the timed-trace monoid, decidable equality of sets of traces, and the
-- inclusion of the naturals as pure delays are shared with plain traces

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Subtrace Op

open WithDecEq _≟ₒ_ using (_≟ᴺ_; _∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The Hoare lower lift of the sub-trace preorder

-- membership and the lifted order are decided, so the lift is stated in
-- the proof-irrelevant `True`-based form: a trace of `xs` is witnessed
-- to be `≼` some trace of `ys` by a `True (any? ...)` proof

infix 5 _≼ˢ_

_≼ˢ_ : List Trace → List Trace → Set
xs ≼ˢ ys = (s : Trace) → True (s ∈? xs) → True (any? (λ t → s ≼? t) ys)

-- the lift of a reflexive relation is reflexive

≼ˢ-refl : {xs : List Trace} → xs ≼ˢ xs
≼ˢ-refl {xs} s m =
  fromWitness (Any.map (λ eq → subst (s ≼_) eq (≼-refl s)) (toWitness m))

-- the lift of a transitive relation is transitive

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
-- The grade order on (non-empty) sets of traces

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces P ≼ˢ traces Q

infix 5 _≾_

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ≼ˢ-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} = ≼ˢ-trans {traces P} {traces Q} {traces R}

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces P} {traces Q} {traces C} {traces C} rel (≼ˢ-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ≼ˢ-·ˢ {traces C} {traces C} {traces P} {traces Q} (≼ˢ-refl {traces C}) rel

------------------------------------------------------------------------
-- Zero-product property
--
-- If `P · Q` lies below `{ ε }`, then every trace of `P` sequenced with
-- some trace of `Q` is `≼ ε`, hence (by minimality of `ε`) equal to the
-- empty trace, so `P` itself lies below `{ ε }` -- and symmetrically.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} hyp s m
  with neHead (traces Q) (nonempty Q)
... | y , y∈Q
        with find (toWitness (hyp (s ∙ y)
                     (fromWitness (∈-cartesianProductWith⁺ _∙_ (toWitness m) y∈Q))))
...     | t , t∈[ε] , sy≼t =
          fromWitness (here (subst (_≼ ε) (sym s≡ε) (≼-refl ε)))
  where
    sy≡ε : (s ∙ y) ≡ ε
    sy≡ε = ≼ε→≡ε (subst ((s ∙ y) ≼_) (∈-[ε]⁻ t∈[ε]) sy≼t)

    s≡ε : s ≡ ε
    s≡ε = ∙-conicalˡ {s} {y} sy≡ε

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} hyp s m
  with neHead (traces P) (nonempty P)
... | x , x∈P
        with find (toWitness (hyp (x ∙ s)
                     (fromWitness (∈-cartesianProductWith⁺ _∙_ x∈P (toWitness m)))))
...     | t , t∈[ε] , xs≼t =
          fromWitness (here (subst (_≼ ε) (sym s≡ε) (≼-refl ε)))
  where
    xs≡ε : (x ∙ s) ≡ ε
    xs≡ε = ≼ε→≡ε (subst ((x ∙ s) ≼_) (∈-[ε]⁻ t∈[ε]) xs≼t)

    s≡ε : s ≡ ε
    s≡ε = ∙-conicalʳ {x} {s} xs≡ε

-- the grade order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} p q =
  fun-ext (λ s → fun-ext (λ m →
    True-irr (any? (λ t → s ≼? t) (traces Q)) (p s m) (q s m)))

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, ordered up to the
-- sub-trace preorder

traces-up-to-subtrace : Grade
traces-up-to-subtrace = record
  { Carrier         = NeTraces
  ; _·_             = _·_
  ; u               = u
  ; ·-identityʳ     = ·-identityʳ
  ; ·-identityˡ     = ·-identityˡ
  ; ·-assoc         = ·-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗ-trans {i} {j} {k}
  ; _≡?_            = _≟ᴺ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵗ-irrelevant {c} {d}
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
