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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_,_; Σ-syntax; _×_; proj₁; proj₂)

open import Syntax.Grades

-- the timed-trace monoid, decidable equality of sets of traces, and the
-- inclusion of the naturals as pure delays are shared with plain traces

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Subtrace Op

open WithDecEq _≟ₒ_ using (_≟ᴺ_)

------------------------------------------------------------------------
-- The Hoare lower lift of the sub-trace preorder

infix 5 _≼ˢ_

_≼ˢ_ : List Trace → List Trace → Set
xs ≼ˢ ys = (s : Trace) → s ∈ xs → Σ[ t ∈ Trace ] (t ∈ ys × s ≼ t)

-- the lift of a reflexive relation is reflexive

≼ˢ-refl : {xs : List Trace} → xs ≼ˢ xs
≼ˢ-refl s s∈ = s , s∈ , ≼-refl s

-- the lift of a transitive relation is transitive

≼ˢ-trans : {xs ys zs : List Trace} → xs ≼ˢ ys → ys ≼ˢ zs → xs ≼ˢ zs
≼ˢ-trans xy yz s s∈ with xy s s∈
... | t , t∈ , s≼t with yz t t∈
... | r , r∈ , t≼r = r , r∈ , ≼-trans s≼t t≼r

-- the language product is monotone for the lift (in both arguments at
-- once), since the trace product is monotone for `_≼_`

≼ˢ-·ˢ : {xs xs' ys ys' : List Trace}
      → xs ≼ˢ xs' → ys ≼ˢ ys' → (xs ·ˢ ys) ≼ˢ (xs' ·ˢ ys')
≼ˢ-·ˢ {xs} {xs'} {ys} {ys'} pxs pys r r∈
  with ∈-cartesianProductWith⁻ _∙_ xs ys r∈
... | a , b , a∈xs , b∈ys , refl with pxs a a∈xs | pys b b∈ys
... | a' , a'∈ , a≼a' | b' , b'∈ , b≼b' =
      a' ∙ b' , ∈-cartesianProductWith⁺ _∙_ a'∈ b'∈ , mono-∙ a≼a' b≼b'

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
≾ᵗ-zero-productˡ {P} {Q} hyp s s∈P
  with neHead (traces Q) (nonempty Q)
... | y , y∈Q with hyp (s ∙ y) (∈-cartesianProductWith⁺ _∙_ s∈P y∈Q)
... | t , t∈[ε] , sy≼t =
      ε , here refl , subst (_≼ ε) (sym s≡ε) (≼-refl ε)
  where
    sy≡ε : (s ∙ y) ≡ ε
    sy≡ε = ≼ε→≡ε (subst (λ z → (s ∙ y) ≼ z) (∈-[ε]⁻ t∈[ε]) sy≼t)

    s≡ε : s ≡ ε
    s≡ε = ∙-conicalˡ {s} {y} sy≡ε

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} hyp s s∈Q
  with neHead (traces P) (nonempty P)
... | x , x∈P with hyp (x ∙ s) (∈-cartesianProductWith⁺ _∙_ x∈P s∈Q)
... | t , t∈[ε] , xs≼t =
      ε , here refl , subst (_≼ ε) (sym s≡ε) (≼-refl ε)
  where
    xs≡ε : (x ∙ s) ≡ ε
    xs≡ε = ≼ε→≡ε (subst (λ z → (x ∙ s) ≼ z) (∈-[ε]⁻ t∈[ε]) xs≼t)

    s≡ε : s ≡ ε
    s≡ε = ∙-conicalʳ {x} {s} xs≡ε

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
  ; of-nat          = of-nat
  ; of-nat-zero     = of-nat-zero
  ; of-nat-plus     = λ {m} {n} → of-nat-plus {m} {n}
  }
