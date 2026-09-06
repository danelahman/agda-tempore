------------------------------------------------------------------------
-- Left-sided (flooring) sets of timed traces, compared by inclusion:  --
--                                                                     --
--   P ≾ Q   iff   every trace of Q is a member of P.                  --
--                                                                     --
-- The mirror image of `Inclusion.RightSided`: the same comparison with --
-- the two sets exchanged. The grade is a *floor* -- it lists the runs  --
-- a computation is required to have -- and weakening asks for fewer of --
-- them, so the inclusion runs `Q ⊆ P`, against the way it is written.  --
--                                                                     --
-- Exchanging the sets is what separates the two one-sided grades of    --
-- this family, and it has to be: flipping the *relation* instead would --
-- not, `_≡_` being symmetric, so the cap's comparison read backwards   --
-- is the cap's comparison again. `LowerLift.LeftSided` relaxes this one --
-- by `_≼_`, in the same exchanged argument order.                     --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Inclusion.LeftSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁻)
open import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.Product using (_,_)

open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (toWitness; fromWitness)

open import Syntax.Grades

-- the carrier and the monoid structure (`_·_`, `u`, `of-nat`, and their
-- laws), decidable equality `_≟ᴺ_`, and the subset preorder itself come
-- from the shared set-of-traces module

open import Syntax.Grades.Traces.Sets Op

open WithDecEq _≟ₒ_

------------------------------------------------------------------------
-- The grade order on (non-empty) sets of traces
--
-- `P ≾ Q` asks that every run `Q` requires be one `P` requires too, so
-- that a weaker floor is one that requires fewer runs.

infix 5 _≾_

_≾_ : NeTraces → NeTraces → Set
P ≾ Q = traces Q ⊑ traces P

≾ᵗ-refl : {P : NeTraces} → P ≾ P
≾ᵗ-refl {P} = ⊑-refl {traces P}

≾ᵗ-trans : {P Q R : NeTraces} → P ≾ Q → Q ≾ R → P ≾ R
≾ᵗ-trans {P} {Q} {R} pq qr = ⊑-trans {traces R} {traces Q} {traces P} qr pq

-- the language product is monotone in both arguments

·-monoˡ : {C P Q : NeTraces} → P ≾ Q → (P · C) ≾ (Q · C)
·-monoˡ {C} {P} {Q} rel =
  ⊑-·ˢ {traces Q} {traces P} {traces C} {traces C} rel (⊑-refl {traces C})

·-monoʳ : {C P Q : NeTraces} → P ≾ Q → (C · P) ≾ (C · Q)
·-monoʳ {C} {P} {Q} rel =
  ⊑-·ˢ {traces C} {traces C} {traces Q} {traces P} (⊑-refl {traces C}) rel

-- the order is proof-irrelevant

≾ᵗ-irrelevant : {P Q : NeTraces} → (p q : P ≾ Q) → p ≡ q
≾ᵗ-irrelevant {P} {Q} = liftˢ-irrelevant

------------------------------------------------------------------------
-- Zero-product property
--
-- A floor of `{ ε }` requires the instantaneous run to be among those
-- listed. If a language product requires it then so does each factor,
-- the trace monoid being conical: the empty run factors only as two
-- empty runs.

≾ᵗ-zero-productˡ : {P Q : NeTraces} → (P · Q) ≾ u → P ≾ u
≾ᵗ-zero-productˡ {P} {Q} hyp s m
  with ∈-[ε]⁻ (toWitness {a? = s ∈? traces u} m)
... | refl
        with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q)
               (toWitness (hyp ε m))
...     | a , b , a∈P , b∈Q , ε≡ab =
          fromWitness
            (Any.map (λ eq → trans (sym (∙-conicalˡ {a} {b} (sym ε≡ab))) eq) a∈P)

≾ᵗ-zero-productʳ : {P Q : NeTraces} → (P · Q) ≾ u → Q ≾ u
≾ᵗ-zero-productʳ {P} {Q} hyp s m
  with ∈-[ε]⁻ (toWitness {a? = s ∈? traces u} m)
... | refl
        with ∈-cartesianProductWith⁻ _∙_ (traces P) (traces Q)
               (toWitness (hyp ε m))
...     | a , b , a∈P , b∈Q , ε≡ab =
          fromWitness
            (Any.map (λ eq → trans (sym (∙-conicalʳ {a} {b} (sym ε≡ab))) eq) b∈Q)

------------------------------------------------------------------------
-- The order is decidable

infix 5 _≾?_

_≾?_ : (P Q : NeTraces) → Dec (P ≾ Q)
P ≾? Q = traces Q ⊑? traces P

------------------------------------------------------------------------
-- The grade of (non-empty) sets of timed traces, read as a floor and
-- compared by inclusion

inclusion-left-sided : Grade
inclusion-left-sided = record
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
