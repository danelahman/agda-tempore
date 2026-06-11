----------------------------------------------------------------------
-- Sets of timed traces of operations as grades (two-sided variant) --
----------------------------------------------------------------------

open import Util.Equality

open import Relation.Binary.Definitions using (DecidableEquality)

module Syntax.Grades.Traces.TwoSidedTraces (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺; ∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades

-- the timed-trace monoid and the set-of-traces monoid are shared

open import Syntax.Grades.Traces.Base Op

------------------------------------------------------------------------
-- The two-sided order and the grade
--
-- The order (and decidable equality of grades) relies on decidable
-- equality of the events, collected in `WithDecEq`.

open WithDecEq _≟ₒ_
 
-- a two-sided trace interval: a lower and an upper non-empty set of
-- timed traces, with the lower set included in the upper set (the
-- analogue of `min ≤ max`)
 
record TraceInterval : Set where
  constructor [_,_,_]
  field
    lower : NeTraces
    upper : NeTraces
    lo⊑up : traces lower ⊑ traces upper

open TraceInterval
 
-- the subset preorder on the underlying lists is proof-irrelevant
 
⊑-irrelevant : {xs ys : List Trace} (p q : xs ⊑ ys) → p ≡ q
⊑-irrelevant {xs} {ys} p q =
  fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? ys) (p s m) (q s m)))
 
-- two intervals are equal as soon as their lower and upper sets are
-- (the inclusion proof is irrelevant)
 
ti-ext : {I J : TraceInterval}
     → lower I ≡ lower J → upper I ≡ upper J → I ≡ J
ti-ext {[ l , h , b ]} {[ .l , .h , b' ]} refl refl = cong [ l , h ,_] (⊑-irrelevant b b')

------------------------------------------------------------------------
-- Monoid structure: componentwise on the lower and the upper set
 
infixl 7 _·ᵀ_
 
_·ᵀ_ : TraceInterval → TraceInterval → TraceInterval
[ l₁ , h₁ , b₁ ] ·ᵀ [ l₂ , h₂ , b₂ ] =
  [ l₁ · l₂ , h₁ · h₂
  , ⊑-·ˢ {traces l₁} {traces h₁} {traces l₂} {traces h₂} b₁ b₂ ]
 
uᵀ : TraceInterval
uᵀ = [ u , u , ⊑-refl {traces u} ]
 
·ᵀ-identityʳ : (I : TraceInterval) → (I ·ᵀ uᵀ) ≡ I
·ᵀ-identityʳ [ l , h , b ] = ti-ext (·-identityʳ l) (·-identityʳ h)
 
·ᵀ-identityˡ : (I : TraceInterval) → (uᵀ ·ᵀ I) ≡ I
·ᵀ-identityˡ [ l , h , b ] = ti-ext (·-identityˡ l) (·-identityˡ h)
 
·ᵀ-assoc : (I J K : TraceInterval) → ((I ·ᵀ J) ·ᵀ K) ≡ (I ·ᵀ (J ·ᵀ K))
·ᵀ-assoc [ l₁ , h₁ , _ ] [ l₂ , h₂ , _ ] [ l₃ , h₃ , _ ] =
  ti-ext (·-assoc l₁ l₂ l₃) (·-assoc h₁ h₂ h₃)

------------------------------------------------------------------------
-- The two-sided (interval-containment) order
--
-- `I ≾ J` when the interval `[ lower I , upper I ]` is contained in
-- `[ lower J , upper J ]`: the lower set grows (superset, left-sided)
-- and the upper set shrinks (subset, right-sided).
 
infix 5 _≾ᵀ_
 
_≾ᵀ_ : TraceInterval → TraceInterval → Set
I ≾ᵀ J = (traces (lower J) ⊑ traces (lower I))
       × (traces (upper I) ⊑ traces (upper J))
 
≾ᵀ-refl : {I : TraceInterval} → I ≾ᵀ I
≾ᵀ-refl = ⊑-refl , ⊑-refl
 
≾ᵀ-trans : {I J K : TraceInterval} → I ≾ᵀ J → J ≾ᵀ K → I ≾ᵀ K
≾ᵀ-trans (lo₁ , hi₁) (lo₂ , hi₂) =
  (λ s m → lo₁ s (lo₂ s m)) , (λ s m → hi₂ s (hi₁ s m))

-- the product is monotone in both arguments
 
·ᵀ-monoˡ : {C I J : TraceInterval} → I ≾ᵀ J → (I ·ᵀ C) ≾ᵀ (J ·ᵀ C)
·ᵀ-monoˡ {C} {I} {J} (lo , hi) =
    ⊑-·ˢ {traces (lower J)} {traces (lower I)}
         {traces (lower C)} {traces (lower C)} lo (⊑-refl {traces (lower C)})
  , ⊑-·ˢ {traces (upper I)} {traces (upper J)}
         {traces (upper C)} {traces (upper C)} hi (⊑-refl {traces (upper C)})
 
·ᵀ-monoʳ : {C I J : TraceInterval} → I ≾ᵀ J → (C ·ᵀ I) ≾ᵀ (C ·ᵀ J)
·ᵀ-monoʳ {C} {I} {J} (lo , hi) =
    ⊑-·ˢ {traces (lower C)} {traces (lower C)}
         {traces (lower J)} {traces (lower I)} (⊑-refl {traces (lower C)}) lo
  , ⊑-·ˢ {traces (upper C)} {traces (upper C)}
         {traces (upper I)} {traces (upper J)} (⊑-refl {traces (upper C)}) hi

-- the order is proof-irrelevant
 
≾ᵀ-irrelevant : {I J : TraceInterval} → (p q : I ≾ᵀ J) → p ≡ q
≾ᵀ-irrelevant (lo₁ , hi₁) (lo₂ , hi₂) =
  cong₂ _,_ (⊑-irrelevant lo₁ lo₂) (⊑-irrelevant hi₁ hi₂)
 
-- decidable equality of grades
 
_≟ᵀ²_ : DecidableEquality TraceInterval
I ≟ᵀ² J with lower I ≟ᴺ lower J | upper I ≟ᴺ upper J
... | yes p | yes q = yes (ti-ext p q)
... | no ¬p | _     = no λ e → ¬p (cong lower e)
... | _     | no ¬q = no λ e → ¬q (cong upper e)

------------------------------------------------------------------------
-- Zero-product property of the order
--
-- It splits into the left-sided fact on the lower component and the
-- right-sided fact on the upper component (the latter relying on
-- non-emptiness of the other factor's upper set).
 
-- lower (left-sided): `{ ε }` included in a product is included in
-- each factor
 
ε∈-·ˢˡ : {xs ys : List Trace} → ((ε ∷ []) ⊑ (xs ·ˢ ys)) → (ε ∷ []) ⊑ xs
ε∈-·ˢˡ {xs} {ys} hyp s mem rewrite ∈-[ε]⁻ (toWitness mem) = fromWitness ε∈xs
  where
    ε∈xy : ε ∈ (xs ·ˢ ys)
    ε∈xy = toWitness (hyp ε (fromWitness {a? = ε ∈? (ε ∷ [])} (here refl)))
 
    ε∈xs : ε ∈ xs
    ε∈xs with ∈-cartesianProductWith⁻ _∙_ xs ys ε∈xy
    ... | a , b , a∈xs , _ , eq = subst (_∈ xs) (∙-conicalˡ {a} {b} (sym eq)) a∈xs

ε∈-·ˢʳ : {xs ys : List Trace} → ((ε ∷ []) ⊑ (xs ·ˢ ys)) → (ε ∷ []) ⊑ ys
ε∈-·ˢʳ {xs} {ys} hyp s mem rewrite ∈-[ε]⁻ (toWitness mem) = fromWitness ε∈ys
  where
    ε∈xy : ε ∈ (xs ·ˢ ys)
    ε∈xy = toWitness (hyp ε (fromWitness {a? = ε ∈? (ε ∷ [])} (here refl)))
 
    ε∈ys : ε ∈ ys
    ε∈ys with ∈-cartesianProductWith⁻ _∙_ xs ys ε∈xy
    ... | a , b , _ , b∈ys , eq = subst (_∈ ys) (∙-conicalʳ {a} {b} (sym eq)) b∈ys
 
-- upper (right-sided): a product included in `{ ε }` has each factor
-- included in `{ ε }`, provided the other factor is non-empty

·ˢ⊑ε-ˡ : {xs ys : List Trace} → NonEmpty ys → ((xs ·ˢ ys) ⊑ (ε ∷ [])) → xs ⊑ (ε ∷ [])
·ˢ⊑ε-ˡ {xs} {ys} ne hyp s mem with neHead ys ne
... | y , y∈ys = fromWitness (here s≡ε)
  where
    sy∈ : (s ∙ y) ∈ (xs ·ˢ ys)
    sy∈ = ∈-cartesianProductWith⁺ _∙_ (toWitness mem) y∈ys
 
    s≡ε : s ≡ ε
    s≡ε = ∙-conicalˡ {s} {y} (∈-[ε]⁻ (toWitness (hyp (s ∙ y) (fromWitness sy∈))))
 
·ˢ⊑ε-ʳ : {xs ys : List Trace} → NonEmpty xs → ((xs ·ˢ ys) ⊑ (ε ∷ [])) → ys ⊑ (ε ∷ [])
·ˢ⊑ε-ʳ {xs} {ys} ne hyp s mem with neHead xs ne
... | x , x∈xs = fromWitness (here s≡ε)
  where
    xs∈ : (x ∙ s) ∈ (xs ·ˢ ys)
    xs∈ = ∈-cartesianProductWith⁺ _∙_ x∈xs (toWitness mem)
 
    s≡ε : s ≡ ε
    s≡ε = ∙-conicalʳ {x} {s} (∈-[ε]⁻ (toWitness (hyp (x ∙ s) (fromWitness xs∈))))

≾ᵀ-zero-productˡ : {I J : TraceInterval} → (I ·ᵀ J) ≾ᵀ uᵀ → I ≾ᵀ uᵀ
≾ᵀ-zero-productˡ {I} {J} (loHyp , hiHyp) =
    ε∈-·ˢˡ {traces (lower I)} {traces (lower J)} loHyp
  , ·ˢ⊑ε-ˡ {traces (upper I)} {traces (upper J)} (nonempty (upper J)) hiHyp
 
≾ᵀ-zero-productʳ : {I J : TraceInterval} → (I ·ᵀ J) ≾ᵀ uᵀ → J ≾ᵀ uᵀ
≾ᵀ-zero-productʳ {I} {J} (loHyp , hiHyp) =
    ε∈-·ˢʳ {traces (lower I)} {traces (lower J)} loHyp
  , ·ˢ⊑ε-ʳ {traces (upper I)} {traces (upper J)} (nonempty (upper I)) hiHyp
 
------------------------------------------------------------------------
-- Inclusion of the natural numbers as (pure-delay) point intervals
 
of-natᵀ : ℕ → TraceInterval
of-natᵀ n = [ of-nat n , of-nat n , ⊑-refl {traces (of-nat n)} ]
 
of-natᵀ-zero : of-natᵀ 0 ≡ uᵀ
of-natᵀ-zero = ti-ext of-nat-zero of-nat-zero
 
of-natᵀ-plus : {m n : ℕ} → of-natᵀ (m + n) ≡ (of-natᵀ m ·ᵀ of-natᵀ n)
of-natᵀ-plus {m} {n} = ti-ext (of-nat-plus {m} {n}) (of-nat-plus {m} {n})

------------------------------------------------------------------------
-- The grade of two-sided sets of timed traces
 
two-sided-traces : Grade
two-sided-traces = record
  { Carrier         = TraceInterval
  ; _·_             = _·ᵀ_
  ; u               = uᵀ
  ; ·-identityʳ     = ·ᵀ-identityʳ
  ; ·-identityˡ     = ·ᵀ-identityˡ
  ; ·-assoc         = ·ᵀ-assoc
  ; _≾_             = _≾ᵀ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵀ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵀ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵀ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵀ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵀ²_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵀ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵀ-zero-productʳ {c} {d}
  ; of-nat          = of-natᵀ
  ; of-nat-zero     = of-natᵀ-zero
  ; of-nat-plus     = λ {m} {n} → of-natᵀ-plus {m} {n}
  }
