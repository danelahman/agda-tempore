-----------------------------------------------------------------------
-- Sets of timed traces of operations as grades (left-sided variant) --
-----------------------------------------------------------------------

open import Util.Equality

module Syntax.Grades.Traces.LeftSidedTraces (Op : Set) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_,_)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades

-- the timed-trace monoid and the set-of-traces monoid are shared

open import Syntax.Grades.Traces.Base Op

------------------------------------------------------------------------
-- Left-sided trace intervals
--
-- A left-sided trace interval `[ P ,⊤⟩` has its lower endpoint the set
-- of traces `P` and its upper endpoint fixed at the set of all traces
-- `⊤` -- the analogue of the time interval `[ n ,+∞⟩`.

data 𝕋ₗ : Set where
  [_,⊤⟩ : NeTraces → 𝕋ₗ

-- the constructor is injective

inj𝕋ₗ : {P Q : NeTraces} → [ P ,⊤⟩ ≡ [ Q ,⊤⟩ → P ≡ Q
inj𝕋ₗ refl = refl

------------------------------------------------------------------------
-- Monoid structure: the language product on the lower set

infixl 7 _·ₗ_

_·ₗ_ : 𝕋ₗ → 𝕋ₗ → 𝕋ₗ
[ P ,⊤⟩ ·ₗ [ Q ,⊤⟩ = [ P · Q ,⊤⟩

uₗ : 𝕋ₗ
uₗ = [ u ,⊤⟩

·ₗ-identityʳ : (I : 𝕋ₗ) → I ·ₗ uₗ ≡ I
·ₗ-identityʳ [ P ,⊤⟩ = cong [_,⊤⟩ (·-identityʳ P)

·ₗ-identityˡ : (I : 𝕋ₗ) → uₗ ·ₗ I ≡ I
·ₗ-identityˡ [ P ,⊤⟩ = cong [_,⊤⟩ (·-identityˡ P)

·ₗ-assoc : (I J K : 𝕋ₗ) → ((I ·ₗ J) ·ₗ K) ≡ (I ·ₗ (J ·ₗ K))
·ₗ-assoc [ P ,⊤⟩ [ Q ,⊤⟩ [ R ,⊤⟩ = cong [_,⊤⟩ (·-assoc P Q R)

-- inclusion of the natural numbers as (pure-delay) point intervals

of-natₗ : ℕ → 𝕋ₗ
of-natₗ n = [ of-nat n ,⊤⟩

of-natₗ-zero : of-natₗ 0 ≡ uₗ
of-natₗ-zero = cong [_,⊤⟩ of-nat-zero

of-natₗ-plus : {m n : ℕ} → of-natₗ (m + n) ≡ (of-natₗ m ·ₗ of-natₗ n)
of-natₗ-plus {m} {n} = cong [_,⊤⟩ (of-nat-plus {m} {n})

------------------------------------------------------------------------
-- The superset order and the grade
--
-- As in the right-sided example, the order (and decidable equality of
-- sets of traces) relies on decidable equality of the events, collected
-- in `WithDecEq`.

module _ (_≟ₒ_ : DecidableEquality Op) where

  open WithDecEq _≟ₒ_

  -- the order on grades is the *superset* order on the lower set (this is
  -- the only place where this example differs from the right-sided one)

  _≾_ : 𝕋ₗ → 𝕋ₗ → Set
  [ P ,⊤⟩ ≾ [ Q ,⊤⟩ = traces Q ⊑ traces P

  infix 5 _≾_

  ≾ᵗ-refl : {I : 𝕋ₗ} → I ≾ I
  ≾ᵗ-refl {[ P ,⊤⟩} s m = m

  ≾ᵗ-trans : {I J K : 𝕋ₗ} → I ≾ J → J ≾ K → I ≾ K
  ≾ᵗ-trans {[ P ,⊤⟩} {[ Q ,⊤⟩} {[ R ,⊤⟩} pq qr s m = pq s (qr s m)

  -- decidable equality of grades

  _≟ₗ_ : DecidableEquality 𝕋ₗ
  [ P ,⊤⟩ ≟ₗ [ Q ,⊤⟩ with P ≟ᴺ Q
  ... | yes p = yes (cong [_,⊤⟩ p)
  ... | no ¬p = no λ e → ¬p (inj𝕋ₗ e)

  -- monotonicity of `_·_` for the superset order: a larger set on the
  -- left is below, so the inclusions run from the `y`-side to the
  -- `x`-side

  ·-monoˡ : {C I J : 𝕋ₗ} → I ≾ J → (I ·ₗ C) ≾ (J ·ₗ C)
  ·-monoˡ {[ C ,⊤⟩} {[ x ,⊤⟩} {[ y ,⊤⟩} rel =
    ⊑-·ˢ {traces y} {traces x} {traces C} {traces C} rel (⊑-refl {traces C})

  ·-monoʳ : {C I J : 𝕋ₗ} → I ≾ J → (C ·ₗ I) ≾ (C ·ₗ J)
  ·-monoʳ {[ C ,⊤⟩} {[ x ,⊤⟩} {[ y ,⊤⟩} rel =
    ⊑-·ˢ {traces C} {traces C} {traces y} {traces x} (⊑-refl {traces C}) rel

  -- the order is proof-irrelevant

  ≾ᵗ-irrelevant : {I J : 𝕋ₗ} → (p q : I ≾ J) → p ≡ q
  ≾ᵗ-irrelevant {[ P ,⊤⟩} {[ Q ,⊤⟩} p q =
    fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? traces P) (p s m) (q s m)))

  -- zero-product property of the order: for the superset order
  -- `(P · Q) ≾ u` says `ε ∈ P · Q`, i.e. there are traces `a ∈ P` and
  -- `b ∈ Q` with `a ∙ b ≡ ε`; conicality of the timed-trace monoid then
  -- gives `a ≡ ε` (resp. `b ≡ ε`), so `ε ∈ P` (resp. `ε ∈ Q`)

  ≾ᵗ-zero-productˡ : {I J : 𝕋ₗ} → (I ·ₗ J) ≾ uₗ → I ≾ uₗ
  ≾ᵗ-zero-productˡ {[ P ,⊤⟩} {[ Q ,⊤⟩} hyp s mem rewrite ∈-[ε]⁻ (toWitness mem) =
    fromWitness ε∈P
    where
      ε∈u : ε ∈ traces u
      ε∈u = here refl

      ε∈PQ : ε ∈ (traces P ·ˢ traces Q)
      ε∈PQ = toWitness (hyp ε (fromWitness {a? = ε ∈? traces u} ε∈u))

      ε∈P : ε ∈ traces P
      ε∈P with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) ε∈PQ
      ... | a , b , a∈P , _ , eq =
            subst (_∈ traces P) (∙-conicalˡ {a} {b} (sym eq)) a∈P

  ≾ᵗ-zero-productʳ : {I J : 𝕋ₗ} → (I ·ₗ J) ≾ uₗ → J ≾ uₗ
  ≾ᵗ-zero-productʳ {[ P ,⊤⟩} {[ Q ,⊤⟩} hyp s mem rewrite ∈-[ε]⁻ (toWitness mem) =
    fromWitness ε∈Q
    where
      ε∈u : ε ∈ traces u
      ε∈u = here refl

      ε∈PQ : ε ∈ (traces P ·ˢ traces Q)
      ε∈PQ = toWitness (hyp ε (fromWitness {a? = ε ∈? traces u} ε∈u))

      ε∈Q : ε ∈ traces Q
      ε∈Q with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) ε∈PQ
      ... | a , b , _ , b∈Q , eq =
            subst (_∈ traces Q) (∙-conicalʳ {a} {b} (sym eq)) b∈Q

  -- the grade of (non-empty) sets of timed traces, ordered by the
  -- superset (left-sided) order

  left-sided-traces-grade : Grade
  left-sided-traces-grade = record
    { Carrier         = 𝕋ₗ
    ; _·_             = _·ₗ_
    ; u               = uₗ
    ; ·-identityʳ     = ·ₗ-identityʳ
    ; ·-identityˡ     = ·ₗ-identityˡ
    ; ·-assoc         = ·ₗ-assoc
    ; _≾_             = _≾_
    ; ·-monoˡ-≾       = λ {c} {x} {y} → ·-monoˡ {c} {x} {y}
    ; ·-monoʳ-≾       = λ {c} {x} {y} → ·-monoʳ {c} {x} {y}
    ; ≾-refl          = λ {x} → ≾ᵗ-refl {x}
    ; ≾-trans         = λ {i} {j} {k} → ≾ᵗ-trans {i} {j} {k}
    ; _≡?_            = _≟ₗ_
    ; ≾-zero-productˡ = λ {c} {d} → ≾ᵗ-zero-productˡ {c} {d}
    ; ≾-zero-productʳ = λ {c} {d} → ≾ᵗ-zero-productʳ {c} {d}
    ; of-nat          = of-natₗ
    ; of-nat-zero     = of-natₗ-zero
    ; of-nat-plus     = λ {m} {n} → of-natₗ-plus {m} {n}
    }
