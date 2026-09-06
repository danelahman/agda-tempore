------------------------------------------------------------------------
-- Sets of timed traces, ordered by inclusion:                         --
--                                                                     --
--   P ≾ Q   iff   every trace of P is a member of Q.                  --
--                                                                     --
-- The only order on sets of traces that needs no cost on the          --
-- operations: it never consults the sub-trace preorder, so a demand    --
-- is discharged only by having done exactly one of the runs listed.    --
-- Weakening a grade only lengthens that list.                          --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.TraceSet.Inclusion
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades

-- the carrier and the monoid structure (`_·_`, `u`, `of-nat`, and their
-- laws), together with decidable equality `_≟ᴺ_`, come from the shared
-- set-of-traces module; only the order below is specific to this grade

open import Syntax.Grades.Traces.Sets Op

------------------------------------------------------------------------
-- The grade
--
-- A grade is a non-empty set of traces `P`, read as an enumeration of
-- the runs after which a boxed resource is available. It is not an
-- interval in either direction: the order compares sets by membership
-- alone, never by the sub-trace preorder, so nothing is bounded above
-- or below -- a demand is discharged only by having done exactly one of
-- the runs listed. The monoid is the language product.

------------------------------------------------------------------------
-- The subset order
--
-- The order (and decidable equality of sets of traces) relies on
-- decidable equality of the events, collected in `WithDecEq`.

open WithDecEq _≟ₒ_

-- the order on grades is the subset order on the listed runs

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces P ⊑ traces Q

infix 5 _≾_

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl s m = m

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans pq qr s m = qr s (pq s m)

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ⊑-·ˢ {traces P} {traces Q} {traces C} {traces C} rel (⊑-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ⊑-·ˢ {traces C} {traces C} {traces P} {traces Q} (⊑-refl {traces C}) rel

-- the order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} p q =
  fun-ext (λ s → fun-ext (λ m → True-irr (s ∈? traces Q) (p s m) (q s m)))

-- zero-product property of the order: if `P · Q ⊆ { ε }` then, since
-- `Q` is non-empty, every trace of `P` sequenced with some trace of
-- `Q` is the empty trace, hence `P ⊆ { ε }` (and symmetrically for `Q`)

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} hyp s mem
  with neHead (traces Q) (nonempty Q)
... | y , y∈Q = fromWitness (here s≡ε)
  where
    sy∈ : (s ∙ y) ∈ (traces P ·ˢ traces Q)
    sy∈ = ∈-cartesianProductWith⁺ _∙_ (toWitness mem) y∈Q

    s≡ε : s ≡ ε
    s≡ε = ∙-conicalˡ {s} {y} (∈-[ε]⁻ (toWitness (hyp (s ∙ y) (fromWitness sy∈))))

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} hyp s mem
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
