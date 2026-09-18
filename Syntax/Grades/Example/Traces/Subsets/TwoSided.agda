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
--                                                                     --
-- No pair is greatest, the floor's own top being the excluded empty    --
-- set of demands, so the carrier carries `unconstrained` above the     --
-- pairs rather than extending either endpoint. It demands nothing and  --
-- permits everything, and it absorbs.                                  --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Subsets.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.Empty using (⊥)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable
  using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Example.Traces.Subsets.Base Op _≟ₒ_

-- each endpoint is ordered exactly as the corresponding one-sided grade
-- orders it

open import Syntax.Grades.Example.Traces.Subsets.LeftSided Op _≟ₒ_
  using () renaming (_≾₀_ to _≾ˡᵒ_; _≾₀?_ to _≾ˡᵒ?_;
                     ≾₀-refl to ≾ˡᵒ-refl; ≾₀-trans to ≾ˡᵒ-trans;
                     ·-monoˡ₀ to ·ˡᵒ-monoˡ; ·-monoʳ₀ to ·ˡᵒ-monoʳ;
                     ≾₀-zero-productˡ to ≾ˡᵒ-zero-productˡ;
                     ≾₀-zero-productʳ to ≾ˡᵒ-zero-productʳ;
                     ≾₀-irrelevant to ≾ˡᵒ-irrelevant)
open import Syntax.Grades.Example.Traces.Subsets.RightSided Op _≟ₒ_
  using () renaming (_≾₀_ to _≾ʰⁱ_; _≾₀?_ to _≾ʰⁱ?_;
                     ≾₀-refl to ≾ʰⁱ-refl; ≾₀-trans to ≾ʰⁱ-trans;
                     ·-monoˡ₀ to ·ʰⁱ-monoˡ; ·-monoʳ₀ to ·ʰⁱ-monoʳ;
                     ≾₀-zero-productˡ to ≾ʰⁱ-zero-productˡ;
                     ≾₀-zero-productʳ to ≾ʰⁱ-zero-productʳ;
                     ≾₀-irrelevant to ≾ʰⁱ-irrelevant)

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
-- The pairs

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
-- The monoid on pairs: the language product on each endpoint

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
-- The order on pairs: each endpoint at its own direction of inclusion

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

_≟ᵇ_ : DecidableEquality TwoSided
i₁ ≟ᵇ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᵇ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

of-natᵇ : ℕ → TwoSided
of-natᵇ n = [ of-nat n , of-nat n , ◇-refl (of-nat n) ]

infix 5 _≾ᵇ?_

_≾ᵇ?_ : (i₁ i₂ : TwoSided) → Dec (i₁ ≾ᵇ i₂)
i₁ ≾ᵇ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The carrier: a written-out pair, or no constraint at all

infix 50 between_

data Interval : Set₀ where
  between_      : TwoSided → Interval
  unconstrained : Interval

between-inj : {i₁ i₂ : TwoSided} → between i₁ ≡ between i₂ → i₁ ≡ i₂
between-inj refl = refl

------------------------------------------------------------------------
-- The monoid, with `unconstrained` absorbing

infixl 7 _·ᴵ_

_·ᴵ_ : Interval → Interval → Interval
(between i₁) ·ᴵ (between i₂) = between (i₁ ·ᵇ i₂)
(between _) ·ᴵ unconstrained = unconstrained
unconstrained ·ᴵ _            = unconstrained

uᴵ : Interval
uᴵ = between uᵇ

·ᴵ-identityʳ : (i : Interval) → i ·ᴵ uᴵ ≡ i
·ᴵ-identityʳ (between i) = cong between_ (·ᵇ-identityʳ i)
·ᴵ-identityʳ unconstrained = refl

·ᴵ-identityˡ : (i : Interval) → uᴵ ·ᴵ i ≡ i
·ᴵ-identityˡ (between i) = cong between_ (·ᵇ-identityˡ i)
·ᴵ-identityˡ unconstrained = refl

·ᴵ-assoc : (i₁ i₂ i₃ : Interval) → (i₁ ·ᴵ i₂) ·ᴵ i₃ ≡ i₁ ·ᴵ (i₂ ·ᴵ i₃)
·ᴵ-assoc (between i₁) (between i₂) (between i₃) =
  cong between_ (·ᵇ-assoc i₁ i₂ i₃)
·ᴵ-assoc (between _) (between _) unconstrained = refl
·ᴵ-assoc (between _) unconstrained (between _) = refl
·ᴵ-assoc (between _) unconstrained unconstrained = refl
·ᴵ-assoc unconstrained _             _             = refl

------------------------------------------------------------------------
-- The order, with `unconstrained` greatest

infix 5 _≾ᴵ_

_≾ᴵ_ : Interval → Interval → Set
(between i₁) ≾ᴵ (between i₂) = i₁ ≾ᵇ i₂
(between _) ≾ᴵ unconstrained = ⊤
unconstrained ≾ᴵ (between _) = ⊥
unconstrained ≾ᴵ unconstrained = ⊤

≾ᴵ-⊤ : (i : Interval) → i ≾ᴵ unconstrained
≾ᴵ-⊤ (between _) = tt
≾ᴵ-⊤ unconstrained = tt

≾ᴵ-refl : {i : Interval} → i ≾ᴵ i
≾ᴵ-refl {between i}   = ≾ᵇ-refl {i}
≾ᴵ-refl {unconstrained} = tt

≾ᴵ-trans : {i₁ i₂ i₃ : Interval} → i₁ ≾ᴵ i₂ → i₂ ≾ᴵ i₃ → i₁ ≾ᴵ i₃
≾ᴵ-trans {between i₁} {between i₂} {between i₃} p q =
  ≾ᵇ-trans {i₁} {i₂} {i₃} p q
≾ᴵ-trans {between _} {between _} {unconstrained} p q = tt
≾ᴵ-trans {between _} {unconstrained} {between _} p ()
≾ᴵ-trans {between _} {unconstrained} {unconstrained} p q = tt
≾ᴵ-trans {unconstrained} {between _} {_} () q
≾ᴵ-trans {unconstrained} {unconstrained} {between _} p ()
≾ᴵ-trans {unconstrained} {unconstrained} {unconstrained} p q = tt

≾ᴵ-irrelevant : {i₁ i₂ : Interval} → (p q : i₁ ≾ᴵ i₂) → p ≡ q
≾ᴵ-irrelevant {between i₁} {between i₂} p  q  = ≾ᵇ-irrelevant {i₁} {i₂} p q
≾ᴵ-irrelevant {between _} {unconstrained} tt tt = refl
≾ᴵ-irrelevant {unconstrained} {between _} () q
≾ᴵ-irrelevant {unconstrained} {unconstrained} tt tt = refl

·ᴵ-monoˡ : {c i₁ i₂ : Interval} → i₁ ≾ᴵ i₂ → (i₁ ·ᴵ c) ≾ᴵ (i₂ ·ᴵ c)
·ᴵ-monoˡ {between c} {between i₁} {between i₂} p = ·ᵇ-monoˡ {c} {i₁} {i₂} p
·ᴵ-monoˡ {unconstrained} {between _} {between _} p = tt
·ᴵ-monoˡ {between _} {between _} {unconstrained} p = tt
·ᴵ-monoˡ {unconstrained} {between _} {unconstrained} p = tt
·ᴵ-monoˡ {_} {unconstrained} {between _} ()
·ᴵ-monoˡ {between _} {unconstrained} {unconstrained} p = tt
·ᴵ-monoˡ {unconstrained} {unconstrained} {unconstrained} p = tt

·ᴵ-monoʳ : {c i₁ i₂ : Interval} → i₁ ≾ᴵ i₂ → (c ·ᴵ i₁) ≾ᴵ (c ·ᴵ i₂)
·ᴵ-monoʳ {between c} {between i₁} {between i₂} p = ·ᵇ-monoʳ {c} {i₁} {i₂} p
·ᴵ-monoʳ {unconstrained} {between _} {between _} p = tt
·ᴵ-monoʳ {between _} {between _} {unconstrained} p = tt
·ᴵ-monoʳ {unconstrained} {between _} {unconstrained} p = tt
·ᴵ-monoʳ {_} {unconstrained} {between _} ()
·ᴵ-monoʳ {between _} {unconstrained} {unconstrained} p = tt
·ᴵ-monoʳ {unconstrained} {unconstrained} {unconstrained} p = tt

------------------------------------------------------------------------
-- Zero-product property
--
-- `unconstrained` is above the unit and not below it, so its clauses
-- are vacuous and the property is the pairs' own.

≾ᴵ-zero-productˡ : {i₁ i₂ : Interval} → (i₁ ·ᴵ i₂) ≾ᴵ uᴵ → i₁ ≾ᴵ uᴵ
≾ᴵ-zero-productˡ {between i₁} {between i₂} p = ≾ᵇ-zero-productˡ {i₁} {i₂} p
≾ᴵ-zero-productˡ {between _} {unconstrained} ()
≾ᴵ-zero-productˡ {unconstrained} {_} ()

≾ᴵ-zero-productʳ : {i₁ i₂ : Interval} → (i₁ ·ᴵ i₂) ≾ᴵ uᴵ → i₂ ≾ᴵ uᴵ
≾ᴵ-zero-productʳ {between i₁} {between i₂} p = ≾ᵇ-zero-productʳ {i₁} {i₂} p
≾ᴵ-zero-productʳ {between _} {unconstrained} ()
≾ᴵ-zero-productʳ {unconstrained} {_} ()

------------------------------------------------------------------------
-- Decidable equality, the inclusion of ℕ, and deciding the order

_≟ᴵ_ : DecidableEquality Interval
(between i₁) ≟ᴵ (between i₂) with i₁ ≟ᵇ i₂
... | yes p = yes (cong between_ p)
... | no ¬p = no λ eq → ¬p (between-inj eq)
(between _) ≟ᴵ unconstrained = no λ ()
unconstrained ≟ᴵ (between _) = no λ ()
unconstrained ≟ᴵ unconstrained = yes refl

of-natᴵ : ℕ → Interval
of-natᴵ n = between (of-natᵇ n)

of-natᴵ-zero : of-natᴵ 0 ≡ uᴵ
of-natᴵ-zero = cong between_ (eqᵇ of-nat-zero of-nat-zero)

of-natᴵ-plus : {m n : ℕ} → of-natᴵ (m + n) ≡ of-natᴵ m ·ᴵ of-natᴵ n
of-natᴵ-plus {m} {n} =
  cong between_ (eqᵇ (of-nat-plus {m} {n}) (of-nat-plus {m} {n}))

infix 5 _≾ᴵ?_

_≾ᴵ?_ : (i₁ i₂ : Interval) → Dec (i₁ ≾ᴵ i₂)
(between i₁) ≾ᴵ? (between i₂) = i₁ ≾ᵇ? i₂
(between _) ≾ᴵ? unconstrained = yes tt
unconstrained ≾ᴵ? (between _) = no λ ()
unconstrained ≾ᴵ? unconstrained = yes tt

------------------------------------------------------------------------
-- The grade of two-sided subset intervals

two-sided : Grade
two-sided = record
  { Carrier         = Interval
  ; _·_             = _·ᴵ_
  ; u               = uᴵ
  ; ·-identityʳ     = ·ᴵ-identityʳ
  ; ·-identityˡ     = ·ᴵ-identityˡ
  ; ·-assoc         = ·ᴵ-assoc
  ; _≾_             = _≾ᴵ_
  ; ⊤               = unconstrained
  ; ≾-⊤             = ≾ᴵ-⊤
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᴵ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᴵ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᴵ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᴵ-trans {i} {j} {k}
  ; _≡?_            = _≟ᴵ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᴵ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᴵ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᴵ-irrelevant {c} {d}
  ; of-nat          = of-natᴵ
  ; of-nat-zero     = of-natᴵ-zero
  ; of-nat-plus     = λ {m} {n} → of-natᴵ-plus {m} {n}
  }
