------------------------------------------------------------------------
-- Sets of timed traces of operations as grades (right-sided variant)  --
--                                                                     --
-- A trace-based counterpart of the time-based right-sided intervals    --
-- `Syntax.Grades.Time.RightSidedIntervals`. A grade is a finite,       --
-- non-empty set of timed traces, where a timed trace is an event       --
-- sequence `⟨ d₁ ⟩ ∙ ⌈ o₁ ⌉ ∙ … ∙ ⌈ oₖ ⌉ ∙ ⟨ dₖ₊₁ ⟩` built from pure  --
-- delays `⟨ d ⟩`, operation events `⌈ o ⌉`, and sequencing `_∙_`.      --
--                                                                     --
-- The timed-trace monoid, the language product on sets of traces, its  --
-- unit `{ ε }`, and the inclusion of the natural numbers as pure       --
-- delays are all shared with the left-sided variant and are re-used    --
-- from `Syntax.Grades.Traces.Base`. The two examples differ only in    --
-- their order, mirroring the time-based intervals: here sets of traces --
-- are ordered by the *subset* order `P ≾ Q  ⟺  P ⊆ Q`, just as the    --
-- right-sided intervals `[0, n ]` are ordered by `m ≤ n`.             --
--                                                                     --
-- The example is parameterised by a `LanguageSpec` (hence by the       --
-- operations and their signatures) together with an assumption that    --
-- the operation symbols have decidable equality. The latter is what    --
-- makes equality of finite sets of timed traces decidable.             --
------------------------------------------------------------------------

open import Syntax.LanguageSpec

open import Util.Equality

module Syntax.Grades.Traces.RightSidedTraces (S : LanguageSpec) where

open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)

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
-- The subset order and the grade
--
-- The order (and decidable equality of sets of traces) relies on
-- decidable equality of the events, collected in `WithDecEq`.

module _ (_≟ₒ_ : DecidableEquality Op) where

  open WithDecEq _≟ₒ_

  -- the order on grades is the subset order

  _≾_ : NeTraces → NeTraces → Set
  P ≾ Q = traces P ⊑ traces Q

  infix 5 _≾_

  ≾ᵗ-refl : {P : NeTraces} → P ≾ P
  ≾ᵗ-refl s m = m

  ≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
  ≾ᵗ-trans pq qr s m = qr s (pq s m)

  -- the language product is monotone in both arguments

  ·-monoˡ : {c x y : NeTraces} → x ≾ y → (x · c) ≾ (y · c)
  ·-monoˡ {c} {x} {y} rel =
    ⊑-·ˢ {traces x} {traces y} {traces c} {traces c} rel (⊑-refl {traces c})

  ·-monoʳ : {c x y : NeTraces} → x ≾ y → (c · x) ≾ (c · y)
  ·-monoʳ {c} {x} {y} rel =
    ⊑-·ˢ {traces c} {traces c} {traces x} {traces y} (⊑-refl {traces c}) rel

  -- the order is proof-irrelevant

  ≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
  ≾ᵗ-irrelevant {P} {Q} p q =
    fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? traces Q) (p s m) (q s m)))

  -- zero-product property of the order: if `P · Q ⊆ { ε }` then, since
  -- `Q` is non-empty, every trace of `P` sequenced with some trace of
  -- `Q` is the empty trace, hence `P ⊆ { ε }` (and symmetrically for `Q`)

  ≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
  ≾ᵗ-zero-productˡ {P} {Q} hyp s mem with neHead (traces Q) (nonempty Q)
  ... | y , y∈Q = fromWitness (here s≡ε)
    where
      sy∈ : (s ∙ y) ∈ (traces P ·ˢ traces Q)
      sy∈ = ∈-cartesianProductWith⁺ _∙_ (toWitness mem) y∈Q

      s≡ε : s ≡ ε
      s≡ε = ∙-conicalˡ (∈-[ε]⁻ (toWitness (hyp (s ∙ y) (fromWitness sy∈))))

  ≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
  ≾ᵗ-zero-productʳ {P} {Q} hyp s mem with neHead (traces P) (nonempty P)
  ... | x , x∈P = fromWitness (here s≡ε)
    where
      xs∈ : (x ∙ s) ∈ (traces P ·ˢ traces Q)
      xs∈ = ∈-cartesianProductWith⁺ _∙_ x∈P (toWitness mem)

      s≡ε : s ≡ ε
      s≡ε = ∙-conicalʳ (∈-[ε]⁻ (toWitness (hyp (x ∙ s) (fromWitness xs∈))))

  -- the grade of (non-empty) sets of timed traces, ordered by inclusion

  right-sided-traces-grade : Grade
  right-sided-traces-grade = record
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
