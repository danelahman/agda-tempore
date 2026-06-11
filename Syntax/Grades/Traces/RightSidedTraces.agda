------------------------------------------------------------------------
-- Sets of timed traces of operations as grades (right-sided variant) --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Traces.RightSidedTraces (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_,_)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades

-- the timed-trace monoid and the set-of-traces monoid are shared

open import Syntax.Grades.Traces.Base Op

------------------------------------------------------------------------
-- One-sided trace intervals
--
-- A right-sided trace interval `[ε, P ]` has its lower endpoint fixed at
-- the unit `{ ε }` (written `ε`) and its upper endpoint the set of
-- traces `P` -- the analogue of the time interval `[0, n ]`.

data 𝕋ᵣ : Set where
  [⦃ε⦄,_] : NeTraces → 𝕋ᵣ

-- the constructor is injective

inj𝕋ᵣ : {P Q : NeTraces} → [⦃ε⦄, P ] ≡ [⦃ε⦄, Q ] → P ≡ Q
inj𝕋ᵣ refl = refl

------------------------------------------------------------------------
-- Monoid structure: the language product on the upper set

infixl 7 _·ᵣ_

_·ᵣ_ : 𝕋ᵣ → 𝕋ᵣ → 𝕋ᵣ
[⦃ε⦄, P ] ·ᵣ [⦃ε⦄, Q ] = [⦃ε⦄, P · Q ]

uᵣ : 𝕋ᵣ
uᵣ = [⦃ε⦄, u ]

·ᵣ-identityʳ : (I : 𝕋ᵣ) → I ·ᵣ uᵣ ≡ I
·ᵣ-identityʳ [⦃ε⦄, P ] = cong [⦃ε⦄,_] (·-identityʳ P)

·ᵣ-identityˡ : (I : 𝕋ᵣ) → uᵣ ·ᵣ I ≡ I
·ᵣ-identityˡ [⦃ε⦄, P ] = cong [⦃ε⦄,_] (·-identityˡ P)

·ᵣ-assoc : (I J K : 𝕋ᵣ) → ((I ·ᵣ J) ·ᵣ K) ≡ (I ·ᵣ (J ·ᵣ K))
·ᵣ-assoc [⦃ε⦄, P ] [⦃ε⦄, Q ] [⦃ε⦄, R ] = cong [⦃ε⦄,_] (·-assoc P Q R)

-- inclusion of the natural numbers as (pure-delay) point intervals

of-natᵣ : ℕ → 𝕋ᵣ
of-natᵣ n = [⦃ε⦄, of-nat n ]

of-natᵣ-zero : of-natᵣ 0 ≡ uᵣ
of-natᵣ-zero = cong [⦃ε⦄,_] of-nat-zero

of-natᵣ-plus : {m n : ℕ} → of-natᵣ (m + n) ≡ (of-natᵣ m ·ᵣ of-natᵣ n)
of-natᵣ-plus {m} {n} = cong [⦃ε⦄,_] (of-nat-plus {m} {n})

------------------------------------------------------------------------
-- The subset order and the grade
--
-- The order (and decidable equality of sets of traces) relies on
-- decidable equality of the events, collected in `WithDecEq`.

open WithDecEq _≟ₒ_
 
-- the order on grades is the subset order on the upper set
 
_≾_ : 𝕋ᵣ → 𝕋ᵣ → Set
[⦃ε⦄, P ] ≾ [⦃ε⦄, Q ] = traces P ⊑ traces Q
 
infix 5 _≾_
 
≾ᵗ-refl : {I : 𝕋ᵣ} → I ≾ I
≾ᵗ-refl {[⦃ε⦄, P ]} s m = m
 
≾ᵗ-trans : {I J K : 𝕋ᵣ} → I ≾ J → J ≾ K → I ≾ K
≾ᵗ-trans {[⦃ε⦄, P ]} {[⦃ε⦄, Q ]} {[⦃ε⦄, R ]} pq qr s m = qr s (pq s m)
 
-- decidable equality of grades
 
_≟ᵣ_ : DecidableEquality 𝕋ᵣ
[⦃ε⦄, P ] ≟ᵣ [⦃ε⦄, Q ] with P ≟ᴺ Q
... | yes p = yes (cong [⦃ε⦄,_] p)
... | no ¬p = no λ e → ¬p (inj𝕋ᵣ e)
 
-- the language product is monotone in both arguments
 
·-monoˡ : {C I J : 𝕋ᵣ} → I ≾ J → (I ·ᵣ C) ≾ (J ·ᵣ C)
·-monoˡ {[⦃ε⦄, C ]} {[⦃ε⦄, x ]} {[⦃ε⦄, y ]} rel =
  ⊑-·ˢ {traces x} {traces y} {traces C} {traces C} rel (⊑-refl {traces C})
 
·-monoʳ : {C I J : 𝕋ᵣ} → I ≾ J → (C ·ᵣ I) ≾ (C ·ᵣ J)
·-monoʳ {[⦃ε⦄, C ]} {[⦃ε⦄, x ]} {[⦃ε⦄, y ]} rel =
  ⊑-·ˢ {traces C} {traces C} {traces x} {traces y} (⊑-refl {traces C}) rel

-- the order is proof-irrelevant
 
≾ᵗ-irrelevant : {I J : 𝕋ᵣ} → (p q : I ≾ J) → p ≡ q
≾ᵗ-irrelevant {[⦃ε⦄, P ]} {[⦃ε⦄, Q ]} p q =
  fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? traces Q) (p s m) (q s m)))
 
-- zero-product property of the order: if `P · Q ⊆ { ε }` then, since
-- `Q` is non-empty, every trace of `P` sequenced with some trace of
-- `Q` is the empty trace, hence `P ⊆ { ε }` (and symmetrically for `Q`)
 
≾ᵗ-zero-productˡ : {I J : 𝕋ᵣ} → (I ·ᵣ J) ≾ uᵣ → I ≾ uᵣ
≾ᵗ-zero-productˡ {[⦃ε⦄, P ]} {[⦃ε⦄, Q ]} hyp s mem
  with neHead (traces Q) (nonempty Q)
... | y , y∈Q = fromWitness (here s≡ε)
  where
    sy∈ : (s ∙ y) ∈ (traces P ·ˢ traces Q)
    sy∈ = ∈-cartesianProductWith⁺ _∙_ (toWitness mem) y∈Q
 
    s≡ε : s ≡ ε
    s≡ε = ∙-conicalˡ {s} {y} (∈-[ε]⁻ (toWitness (hyp (s ∙ y) (fromWitness sy∈))))
 
≾ᵗ-zero-productʳ : {I J : 𝕋ᵣ} → (I ·ᵣ J) ≾ uᵣ → J ≾ uᵣ
≾ᵗ-zero-productʳ {[⦃ε⦄, P ]} {[⦃ε⦄, Q ]} hyp s mem
  with neHead (traces P) (nonempty P)
... | x , x∈P = fromWitness (here s≡ε)
  where
    xs∈ : (x ∙ s) ∈ (traces P ·ˢ traces Q)
    xs∈ = ∈-cartesianProductWith⁺ _∙_ x∈P (toWitness mem)
 
    s≡ε : s ≡ ε
    s≡ε = ∙-conicalʳ {x} {s} (∈-[ε]⁻ (toWitness (hyp (x ∙ s) (fromWitness xs∈))))

-- the grade of (non-empty) sets of timed traces, ordered by inclusion
 
right-sided-traces : Grade
right-sided-traces = record
  { Carrier         = 𝕋ᵣ
  ; _·_             = _·ᵣ_
  ; u               = uᵣ
  ; ·-identityʳ     = ·ᵣ-identityʳ
  ; ·-identityˡ     = ·ᵣ-identityˡ
  ; ·-assoc         = ·ᵣ-assoc
  ; _≾_             = _≾_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵗ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵗ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵣ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗ-zero-productʳ {c} {d}
  ; of-nat          = of-natᵣ
  ; of-nat-zero     = of-natᵣ-zero
  ; of-nat-plus     = λ {m} {n} → of-natᵣ-plus {m} {n}
  }
