------------------------------------------------------------------------
-- Two-sided trace intervals compared by the Smyth upper lift.         --
--                                                                     --
-- The mirror of `LowerLift.TwoSided`: a grade is a *pair* of sets of   --
-- traces, `[ lo , hi ]`, bounding a run from both sides, with each      --
-- endpoint compared by `_≽ˢ_` rather than `_≼ˢ_` -- one lift, in       --
-- opposite argument orders:                                           --
--                                                                     --
--   [ L₁ , U₁ ] ≾ [ L₂ , U₂ ]   iff   L₂ ≽ˢ L₁   and   U₁ ≽ˢ U₂      --
--                                                                     --
-- so the floor may still drop and the cap may still rise, but the      --
-- quantifier now runs over the other set of each pair: it is the       --
-- *listed* bounds that must be justified, rather than each of them     --
-- finding a witness.                                                   --
--                                                                     --
-- The consistency field `lo≽hi` is this lift's analogue of `min≤max`:  --
-- every trace the cap permits has one the floor requires inside it, so --
-- the interval is inhabited.                                          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.UpperLift.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (cost : Op → ℕ) where

open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost

-- each endpoint is ordered exactly as the corresponding one-sided
-- upper-lift grade orders it

open import Syntax.Grades.Example.Traces.UpperLift.LeftSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_;
                     ≾ᵗ-zero-productˡ to ≾ˡᵒ-zero-productˡ;
                     ≾ᵗ-zero-productʳ to ≾ˡᵒ-zero-productʳ)
open import Syntax.Grades.Example.Traces.UpperLift.RightSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_;
                     ≾ᵗ-zero-productˡ to ≾ʰⁱ-zero-productˡ;
                     ≾ᵗ-zero-productʳ to ≾ʰⁱ-zero-productʳ)

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The carrier

record UpperInterval : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- every permitted run has a required one inside it
    lo≽hi : traces lo ≽ˢ traces hi

open UpperInterval public

-- two intervals are equal as soon as their endpoints are: the
-- consistency witness is a `True`-of-a-decision, hence irrelevant

lo≽hi-irr : {L U : NeTraces} (p q : traces L ≽ˢ traces U) → p ≡ q
lo≽hi-irr {L} {U} = liftˢ-irrelevant

eqᵘⁱ : {i₁ i₂ : UpperInterval} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᵘⁱ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (lo≽hi-irr {L} {U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᵘⁱ_

_·ᵘⁱ_ : UpperInterval → UpperInterval → UpperInterval
i₁ ·ᵘⁱ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ≽ˢ-·ˢ {traces (lo i₁)} {traces (hi i₁)} {traces (lo i₂)} {traces (hi i₂)}
          (lo≽hi i₁) (lo≽hi i₂)
  ]

uᵘⁱ : UpperInterval
uᵘⁱ = [ u , u , ≽ˢ-refl {traces u} ]

·ᵘⁱ-identityʳ : (i : UpperInterval) → (i ·ᵘⁱ uᵘⁱ) ≡ i
·ᵘⁱ-identityʳ i = eqᵘⁱ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ᵘⁱ-identityˡ : (i : UpperInterval) → (uᵘⁱ ·ᵘⁱ i) ≡ i
·ᵘⁱ-identityˡ i = eqᵘⁱ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ᵘⁱ-assoc : (i₁ i₂ i₃ : UpperInterval)
          → ((i₁ ·ᵘⁱ i₂) ·ᵘⁱ i₃) ≡ (i₁ ·ᵘⁱ (i₂ ·ᵘⁱ i₃))
·ᵘⁱ-assoc i₁ i₂ i₃ =
  eqᵘⁱ (·-assoc (lo i₁) (lo i₂) (lo i₃))
       (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: the floor drops, the cap rises

infix 5 _≾ᵘⁱ_

_≾ᵘⁱ_ : UpperInterval → UpperInterval → Set
i₁ ≾ᵘⁱ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

≾ᵘⁱ-refl : {i : UpperInterval} → i ≾ᵘⁱ i
≾ᵘⁱ-refl {i} = ≽ˢ-refl {traces (lo i)} , ≽ˢ-refl {traces (hi i)}

≾ᵘⁱ-trans : {i₁ i₂ i₃ : UpperInterval} → i₁ ≾ᵘⁱ i₂ → i₂ ≾ᵘⁱ i₃ → i₁ ≾ᵘⁱ i₃
≾ᵘⁱ-trans {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ≽ˢ-trans {traces (lo i₃)} {traces (lo i₂)} {traces (lo i₁)} l₂ l₁
  , ≽ˢ-trans {traces (hi i₁)} {traces (hi i₂)} {traces (hi i₃)} h₁ h₂

-- the product is monotone endpoint by endpoint

·ᵘⁱ-monoˡ : {c i₁ i₂ : UpperInterval} → i₁ ≾ᵘⁱ i₂ → (i₁ ·ᵘⁱ c) ≾ᵘⁱ (i₂ ·ᵘⁱ c)
·ᵘⁱ-monoˡ {c} {i₁} {i₂} (l , h) =
    ≽ˢ-·ˢ {traces (lo i₂)} {traces (lo i₁)} {traces (lo c)} {traces (lo c)}
          l (≽ˢ-refl {traces (lo c)})
  , ≽ˢ-·ˢ {traces (hi i₁)} {traces (hi i₂)} {traces (hi c)} {traces (hi c)}
          h (≽ˢ-refl {traces (hi c)})

·ᵘⁱ-monoʳ : {c i₁ i₂ : UpperInterval} → i₁ ≾ᵘⁱ i₂ → (c ·ᵘⁱ i₁) ≾ᵘⁱ (c ·ᵘⁱ i₂)
·ᵘⁱ-monoʳ {c} {i₁} {i₂} (l , h) =
    ≽ˢ-·ˢ {traces (lo c)} {traces (lo c)} {traces (lo i₂)} {traces (lo i₁)}
          (≽ˢ-refl {traces (lo c)}) l
  , ≽ˢ-·ˢ {traces (hi c)} {traces (hi c)} {traces (hi i₁)} {traces (hi i₂)}
          (≽ˢ-refl {traces (hi c)}) h

------------------------------------------------------------------------
-- Zero-product property
--
-- Only the cap carries information at the unit, as in
-- `LowerLift.TwoSided`: the floor half is `UpperLift.LeftSided`'s,
-- which is vacuous, and the cap half is `UpperLift.RightSided`'s.

≾ᵘⁱ-zero-productˡ : {i₁ i₂ : UpperInterval} → (i₁ ·ᵘⁱ i₂) ≾ᵘⁱ uᵘⁱ → i₁ ≾ᵘⁱ uᵘⁱ
≾ᵘⁱ-zero-productˡ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productˡ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productˡ {hi i₁} {hi i₂} h

≾ᵘⁱ-zero-productʳ : {i₁ i₂ : UpperInterval} → (i₁ ·ᵘⁱ i₂) ≾ᵘⁱ uᵘⁱ → i₂ ≾ᵘⁱ uᵘⁱ
≾ᵘⁱ-zero-productʳ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productʳ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productʳ {hi i₁} {hi i₂} h

-- both halves are decided, so the order is proof-irrelevant

≾ᵘⁱ-irrelevant : {i₁ i₂ : UpperInterval} → (p q : i₁ ≾ᵘⁱ i₂) → p ≡ q
≾ᵘⁱ-irrelevant {i₁} {i₂} (l , h) (l' , h') =
  cong₂ _,_ (liftˢ-irrelevant l l') (liftˢ-irrelevant h h')

-- decidable equality, endpoint by endpoint

_≟ᵘⁱ_ : Decidable (_≡_ {A = UpperInterval})
i₁ ≟ᵘⁱ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᵘⁱ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers
--
-- `n` time steps is the singleton interval at the pure delay `⟨ n ⟩`.

of-natᵘⁱ : ℕ → UpperInterval
of-natᵘⁱ n = [ of-nat n , of-nat n , ≽ˢ-refl {traces (of-nat n)} ]

------------------------------------------------------------------------
-- The order is decidable, endpoint by endpoint

infix 5 _≾ᵘⁱ?_

_≾ᵘⁱ?_ : (i₁ i₂ : UpperInterval) → Dec (i₁ ≾ᵘⁱ i₂)
i₁ ≾ᵘⁱ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of two-sided upper-lift trace intervals

upper-lift-two-sided : Grade
upper-lift-two-sided = record
  { Carrier         = UpperInterval
  ; _·_             = _·ᵘⁱ_
  ; u               = uᵘⁱ
  ; ·-identityʳ     = ·ᵘⁱ-identityʳ
  ; ·-identityˡ     = ·ᵘⁱ-identityˡ
  ; ·-assoc         = ·ᵘⁱ-assoc
  ; _≾_             = _≾ᵘⁱ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᵘⁱ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᵘⁱ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᵘⁱ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᵘⁱ-trans {i} {j} {k}
  ; _≡?_            = _≟ᵘⁱ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᵘⁱ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᵘⁱ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᵘⁱ-irrelevant {c} {d}
  ; of-nat          = of-natᵘⁱ
  ; of-nat-zero     = eqᵘⁱ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqᵘⁱ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }
