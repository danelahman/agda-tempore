------------------------------------------------------------------------
-- Sets of timed traces of operations as grades (left-sided variant)   --
--                                                                     --
-- Left-sided counterpart of `Syntax.Grades.Traces.RightSidedTraces`.  --
-- As there, a grade is a finite, non-empty set of timed traces, where --
-- a timed trace is an event sequence                                  --
-- `⟨ d₁ ⟩ ∙ ⌈ o₁ ⌉ ∙ … ∙ ⌈ oₖ ⌉ ∙ ⟨ dₖ₊₁ ⟩` built from pure delays    --
-- `⟨ d ⟩`, operation events `⌈ o ⌉`, and sequencing `_∙_`. The         --
-- timed-trace monoid, the language product on sets of traces, its unit --
-- `{ ε }`, and the inclusion of the natural numbers as pure delays are --
-- all shared with the right-sided variant and are re-used from         --
-- `Syntax.Grades.Traces.Base`.                                         --
--                                                                     --
-- The two examples differ in exactly one place: the order. This is the --
-- same distinction as between the time-based one-sided intervals,      --
-- where the right-sided intervals `[0, n ]` are ordered by `m ≤ n` and --
-- the left-sided intervals `[ n ,+∞⟩` are ordered by the reverse       --
-- `n ≤ m`. Concretely:                                                 --
--                                                                     --
--   * the right-sided example (`RightSidedTraces`) orders sets of     --
--     traces by the subset order `P ≾ Q  ⟺  P ⊆ Q`;                   --
--   * this left-sided example orders them by the superset order        --
--     `P ≾ Q  ⟺  Q ⊆ P`.                                              --
--                                                                     --
-- Whereas in the time-based intervals reversing the order made the     --
-- zero-product property trivial (the unit `[ 0 ,+∞⟩` becomes the top), --
-- here it stays interesting: `(P · Q) ≾ u` now reads `ε ∈ P · Q`, and  --
-- recovering `ε ∈ P` (resp. `ε ∈ Q`) relies on the conicality of the   --
-- timed-trace monoid, just as the right-sided example relied on it to  --
-- prove the dual `P · Q ⊆ { ε } ⇒ P ⊆ { ε }`.                         --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Grades.Traces.LeftSidedTraces (S : LanguageSpec) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any using (here)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades
open import Syntax.Operations

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

-- the timed-trace monoid and the set-of-traces monoid are shared

open import Syntax.Grades.Traces.Base S

------------------------------------------------------------------------
-- The superset order and the grade
--
-- As in the right-sided example, the order (and decidable equality of
-- sets of traces) relies on decidable equality of the events, collected
-- in `WithDecEq`.

module _ (_≟ₒ_ : DecidableEquality Op) where

  open WithDecEq _≟ₒ_

  -- the order on grades is the *superset* order (this is the only place
  -- where this example differs from the right-sided one)

  _≾_ : NeTraces → NeTraces → Set
  P ≾ Q = traces Q ⊑ traces P

  infix 5 _≾_

  ≾ᵗ-refl : {P : NeTraces} → P ≾ P
  ≾ᵗ-refl s m = m

  ≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
  ≾ᵗ-trans pq qr s m = pq s (qr s m)

  -- monotonicity of `_·_` for the superset order: a larger set on the
  -- left is below, so the inclusions run from the `y`-side to the
  -- `x`-side

  ·-monoˡ : {c x y : NeTraces} → x ≾ y → (x · c) ≾ (y · c)
  ·-monoˡ {c} {x} {y} rel =
    ⊑-·ˢ {traces y} {traces x} {traces c} {traces c} rel (⊑-refl {traces c})

  ·-monoʳ : {c x y : NeTraces} → x ≾ y → (c · x) ≾ (c · y)
  ·-monoʳ {c} {x} {y} rel =
    ⊑-·ˢ {traces c} {traces c} {traces y} {traces x} (⊑-refl {traces c}) rel

  -- the order is proof-irrelevant

  ≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
  ≾ᵗ-irrelevant {P} {Q} p q =
    fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? traces P) (p s m) (q s m)))

  -- zero-product property of the order: for the superset order
  -- `(P · Q) ≾ u` says `ε ∈ P · Q`, i.e. there are traces `a ∈ P` and
  -- `b ∈ Q` with `a ∙ b ≡ ε`; conicality of the timed-trace monoid then
  -- gives `a ≡ ε` (resp. `b ≡ ε`), so `ε ∈ P` (resp. `ε ∈ Q`)

  ≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
  ≾ᵗ-zero-productˡ {P} {Q} hyp s mem rewrite ∈-[ε]⁻ (toWitness mem) =
    fromWitness ε∈P
    where
      ε∈PQ : ε ∈ (traces P ·ˢ traces Q)
      ε∈PQ = toWitness (hyp ε (fromWitness (here refl)))

      ε∈P : ε ∈ traces P
      ε∈P with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) ε∈PQ
      ... | a , b , a∈P , _ , eq =
            subst (_∈ traces P) (∙-conicalˡ (sym eq)) a∈P

  ≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
  ≾ᵗ-zero-productʳ {P} {Q} hyp s mem rewrite ∈-[ε]⁻ (toWitness mem) =
    fromWitness ε∈Q
    where
      ε∈PQ : ε ∈ (traces P ·ˢ traces Q)
      ε∈PQ = toWitness (hyp ε (fromWitness (here refl)))

      ε∈Q : ε ∈ traces Q
      ε∈Q with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q) ε∈PQ
      ... | a , b , _ , b∈Q , eq =
            subst (_∈ traces Q) (∙-conicalʳ (sym eq)) b∈Q

  -- the grade of (non-empty) sets of timed traces, ordered by the
  -- superset (left-sided) order

  left-sided-traces-grade : Grade
  left-sided-traces-grade = record
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
