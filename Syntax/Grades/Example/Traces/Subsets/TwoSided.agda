------------------------------------------------------------------------
-- Sets of timed traces bounding a computation from both sides, at the --
-- subset order.                                                       --
--                                                                     --
-- A grade is a pair `[ P , Q ]` of non-empty finite sets of traces,    --
-- read against the runs `X` a computation may have as                  --
--                                                                     --
--   P ⊆ X ⊆ Q                                                          --
--                                                                     --
-- -- each listed trace of `P` is a run the computation can exhibit,    --
-- and every run it has is listed in `Q`. This is the Egli-Milner       --
-- reading, and it is a genuine interval: the grades between `P` and    --
-- `Q` in the subset lattice are exactly the run-sets it admits.        --
--                                                                     --
-- The endpoints move in opposite directions,                           --
--                                                                     --
--   [ P , Q ] ≾ [ P' , Q' ]   iff   P' ⊆ P   and   Q ⊆ Q'              --
--                                                                     --
-- so the floor is read conjunctively (dropping a member weakens) and   --
-- the cap disjunctively (gaining one weakens). The unit is `[{ε},{ε}]` --
-- -- the computation stops, and can.                                   --
--                                                                     --
-- COHERENCE. The field asks `P ⊆ Q`. Here that is not merely necessary --
-- but exactly right: `P ⊆ X ⊆ Q` has a solution iff `P ⊆ Q` (take      --
-- `X := Q`), so the field refuses precisely the uninhabited grades.    --
-- `Traces.Timed.TwoSided` can only manage necessity, its two endpoints --
-- being ordered by incomparable relations; with one order on both      --
-- sides the interval closes exactly.                                   --
--                                                                     --
-- READINGS. As an *effect* grade, `Q` lists what may happen and `P`    --
-- what must remain reachable; `coerce` adds runs above and forgets     --
-- reachability below. As a *resource* grade, `unbox`'s `ρ' ≾ᵣ ρ` asks  --
-- the elapsed grade to keep every run the box demands available while  --
-- introducing none the box does not list.                              --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_

-- each endpoint is ordered exactly as the corresponding one-sided grade
-- orders it

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using () renaming (_≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_;
                     ≾-refl to ≾ˡᵒ-refl; ≾-trans to ≾ˡᵒ-trans;
                     ·-monoˡ to ·ˡᵒ-monoˡ; ·-monoʳ to ·ˡᵒ-monoʳ;
                     ≾-zero-productˡ to ≾ˡᵒ-zero-productˡ;
                     ≾-zero-productʳ to ≾ˡᵒ-zero-productʳ;
                     ≾-irrelevant to ≾ˡᵒ-irrelevant)
open import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_
  using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_;
                     ≾-refl to ≾ʰⁱ-refl; ≾-trans to ≾ʰⁱ-trans;
                     ·-monoˡ to ·ʰⁱ-monoˡ; ·-monoʳ to ·ʰⁱ-monoʳ;
                     ≾-zero-productˡ to ≾ʰⁱ-zero-productˡ;
                     ≾-zero-productʳ to ≾ʰⁱ-zero-productʳ;
                     ≾-irrelevant to ≾ʰⁱ-irrelevant)

open WithDecEq _≟ₒ_
  using (_⊑_; _⊑?_; ⊑-refl; ⊑-trans; ⊑-·ˢ; _≟ᴺ_; True-irr)

------------------------------------------------------------------------
-- Coherence
--
-- Stated in the decided form so a grade can be written down with `tt`
-- and so the field is irrelevant.

infix 5 _◇_

_◇_ : List Trace → List Trace → Set
xs ◇ ys = True (xs ⊑? ys)

◇-irr : {xs ys : List Trace} → (p q : xs ◇ ys) → p ≡ q
◇-irr {xs} {ys} = True-irr (xs ⊑? ys)

◇-refl : (P : NeTraces) → traces P ◇ traces P
◇-refl P = fromWitness (⊑-refl {traces P})

◇-·ˢ : {xs xs' ys ys' : List Trace}
     → xs ◇ ys → xs' ◇ ys' → (xs ·ˢ xs') ◇ (ys ·ˢ ys')
◇-·ˢ p q = fromWitness (⊑-·ˢ (toWitness p) (toWitness q))

------------------------------------------------------------------------
-- The carrier

record TwoSided : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- every demanded run is a permitted one, which is exactly what it
    -- takes for some run-set to sit between the two
    lo◇hi : traces lo ◇ traces hi

open TwoSided public

eqᵇ : {i₁ i₂ : TwoSided} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵇ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (◇-irr {traces L} {traces U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵇ_

_·ᵇ_ : TwoSided → TwoSided → TwoSided
i₁ ·ᵇ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ◇-·ˢ {traces (lo i₁)} {traces (lo i₂)} {traces (hi i₁)} {traces (hi i₂)}
         (lo◇hi i₁) (lo◇hi i₂)
  ]

uᵇ : TwoSided
uᵇ = [ u , u , ◇-refl u ]

·ᵇ-identityʳ : (i : TwoSided) → (i ·ᵇ uᵇ) ≡ i
·ᵇ-identityʳ i = eqᵇ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ᵇ-identityˡ : (i : TwoSided) → (uᵇ ·ᵇ i) ≡ i
·ᵇ-identityˡ i = eqᵇ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ᵇ-assoc : (i₁ i₂ i₃ : TwoSided) → ((i₁ ·ᵇ i₂) ·ᵇ i₃) ≡ (i₁ ·ᵇ (i₂ ·ᵇ i₃))
·ᵇ-assoc i₁ i₂ i₃ =
  eqᵇ (·-assoc (lo i₁) (lo i₂) (lo i₃)) (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: each endpoint at its own direction of inclusion

infix 5 _≾ᵇ_

_≾ᵇ_ : TwoSided → TwoSided → Set
i₁ ≾ᵇ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

≾ᵇ-refl : {i : TwoSided} → i ≾ᵇ i
≾ᵇ-refl {i} = ≾ˡᵒ-refl {lo i} , ≾ʰⁱ-refl {hi i}

≾ᵇ-trans : {i₁ i₂ i₃ : TwoSided} → i₁ ≾ᵇ i₂ → i₂ ≾ᵇ i₃ → i₁ ≾ᵇ i₃
≾ᵇ-trans {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ≾ˡᵒ-trans {lo i₁} {lo i₂} {lo i₃} l₁ l₂
  , ≾ʰⁱ-trans {hi i₁} {hi i₂} {hi i₃} h₁ h₂

·ᵇ-monoˡ : {c i₁ i₂ : TwoSided} → i₁ ≾ᵇ i₂ → (i₁ ·ᵇ c) ≾ᵇ (i₂ ·ᵇ c)
·ᵇ-monoˡ {c} {i₁} {i₂} (l , h) =
    ·ˡᵒ-monoˡ {lo c} {lo i₁} {lo i₂} l , ·ʰⁱ-monoˡ {hi c} {hi i₁} {hi i₂} h

·ᵇ-monoʳ : {c i₁ i₂ : TwoSided} → i₁ ≾ᵇ i₂ → (c ·ᵇ i₁) ≾ᵇ (c ·ᵇ i₂)
·ᵇ-monoʳ {c} {i₁} {i₂} (l , h) =
    ·ˡᵒ-monoʳ {lo c} {lo i₁} {lo i₂} l , ·ʰⁱ-monoʳ {hi c} {hi i₁} {hi i₂} h

-- the coherence field travels along the order: weakening shrinks the
-- floor and grows the cap, so the two endpoints only move apart

◇-≾ : (i : TwoSided) (L U : NeTraces)
    → lo i ≾ˡᵒ L → hi i ≾ʰⁱ U → traces L ◇ traces U
◇-≾ i L U l h =
  fromWitness
    (⊑-trans l (⊑-trans {traces (lo i)} {traces (hi i)} (toWitness (lo◇hi i)) h))

------------------------------------------------------------------------
-- Zero-product, endpointwise

≾ᵇ-zero-productˡ : {i₁ i₂ : TwoSided} → (i₁ ·ᵇ i₂) ≾ᵇ uᵇ → i₁ ≾ᵇ uᵇ
≾ᵇ-zero-productˡ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productˡ {lo i₁} {lo i₂} l , ≾ʰⁱ-zero-productˡ {hi i₁} {hi i₂} h

≾ᵇ-zero-productʳ : {i₁ i₂ : TwoSided} → (i₁ ·ᵇ i₂) ≾ᵇ uᵇ → i₂ ≾ᵇ uᵇ
≾ᵇ-zero-productʳ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productʳ {lo i₁} {lo i₂} l , ≾ʰⁱ-zero-productʳ {hi i₁} {hi i₂} h

≾ᵇ-irrelevant : {i₁ i₂ : TwoSided} → (p q : i₁ ≾ᵇ i₂) → p ≡ q
≾ᵇ-irrelevant {i₁} {i₂} (l , h) (l' , h') =
  cong₂ _,_ (≾ˡᵒ-irrelevant {lo i₁} {lo i₂} l l')
            (≾ʰⁱ-irrelevant {hi i₁} {hi i₂} h h')

_≟ᵇ_ : Decidable (_≡_ {A = TwoSided})
i₁ ≟ᵇ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᵇ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers, and deciding the order

of-natᵇ : ℕ → TwoSided
of-natᵇ n = [ of-nat n , of-nat n , ◇-refl (of-nat n) ]

infix 5 _≾ᵇ?_

_≾ᵇ?_ : (i₁ i₂ : TwoSided) → Dec (i₁ ≾ᵇ i₂)
i₁ ≾ᵇ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of two-sided subset intervals

two-sided : Grade
two-sided = record
  { Carrier         = TwoSided
  ; _·_             = _·ᵇ_
  ; u               = uᵇ
  ; ·-identityʳ     = ·ᵇ-identityʳ
  ; ·-identityˡ     = ·ᵇ-identityˡ
  ; ·-assoc         = ·ᵇ-assoc
  ; _≾_             = _≾ᵇ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵇ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵇ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵇ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵇ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵇ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵇ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵇ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵇ-irrelevant {c} {d}
  ; of-nat          = of-natᵇ
  ; of-nat-zero     = eqᵇ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqᵇ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }
