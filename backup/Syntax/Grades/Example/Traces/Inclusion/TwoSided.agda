------------------------------------------------------------------------
-- Two-sided inclusion intervals as grades.                            --
--                                                                     --
-- A grade is a *pair* of sets of traces, `[ lo , hi ]`, bounding the   --
-- runs of a computation from both sides by membership alone:          --
--                                                                     --
--   * `lo` is a floor -- every run it lists must be among those had;  --
--   * `hi` is a cap  -- no run may be had beyond those it lists.      --
--                                                                     --
-- The consistency field `lo⊑hi` is the analogue of `min≤max`: what is  --
-- required must be permitted, or the interval is empty. It is stricter --
-- than `LowerLift.TwoSided`'s `lo≼hi`, which asks only that the floor  --
-- be *covered* by the cap, so a pair well-formed there need not be     --
-- well-formed here: `[ { ab , a } , { abcd } ]` is a subtrace interval  --
-- and not an inclusion one. That is the column's defining property     --
-- showing through, membership being all it ever consults.              --
--                                                                     --
-- The order weakens each endpoint outwards, with `⊆` where            --
-- `Time.TwoSided` has `_≤_` and, as there, the two endpoints       --
-- compared in *opposite* directions:                                  --
--                                                                     --
--   [ L₁ , U₁ ] ≾ [ L₂ , U₂ ]   iff   L₂ ⊆ L₁   and   U₁ ⊆ U₂        --
--                                                                     --
-- so the floor may drop a requirement and the cap may gain a           --
-- permission. `LowerLift.TwoSided` is this grade with both endpoints    --
-- relaxed by `_≼_`, in the same two argument orders.                  --
------------------------------------------------------------------------

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

module Syntax.Grades.Example.Traces.Inclusion.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) where

open import Data.Nat.Base using (ℕ)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op

-- each endpoint is ordered exactly as the corresponding one-sided
-- inclusion grade orders it

open import Syntax.Grades.Example.Traces.Inclusion.LeftSided Op _≟ₒ_
  using () renaming (_≾_ to _≾ˡᵒ_; _≾?_ to _≾ˡᵒ?_;
                     ≾ᵗ-zero-productˡ to ≾ˡᵒ-zero-productˡ;
                     ≾ᵗ-zero-productʳ to ≾ˡᵒ-zero-productʳ)
open import Syntax.Grades.Example.Traces.Inclusion.RightSided Op _≟ₒ_
  using () renaming (_≾_ to _≾ʰⁱ_; _≾?_ to _≾ʰⁱ?_;
                     ≾ᵗ-zero-productˡ to ≾ʰⁱ-zero-productˡ;
                     ≾ᵗ-zero-productʳ to ≾ʰⁱ-zero-productʳ)

open WithDecEq _≟ₒ_

------------------------------------------------------------------------
-- The carrier

record InclusionInterval : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- what the floor requires, the cap already permits
    lo⊑hi : traces lo ⊑ traces hi

open InclusionInterval public

-- two intervals are equal as soon as their endpoints are: the
-- consistency witness is a `True`-of-a-decision, hence irrelevant

lo⊑hi-irr : {L U : NeTraces} (p q : traces L ⊑ traces U) → p ≡ q
lo⊑hi-irr {L} {U} = liftˢ-irrelevant

eqⁱⁱ : {i₁ i₂ : InclusionInterval} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqⁱⁱ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (lo⊑hi-irr {L} {U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ⁱⁱ_

_·ⁱⁱ_ : InclusionInterval → InclusionInterval → InclusionInterval
i₁ ·ⁱⁱ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ⊑-·ˢ {traces (lo i₁)} {traces (hi i₁)} {traces (lo i₂)} {traces (hi i₂)}
         (lo⊑hi i₁) (lo⊑hi i₂)
  ]

uⁱⁱ : InclusionInterval
uⁱⁱ = [ u , u , ⊑-refl {traces u} ]

·ⁱⁱ-identityʳ : (i : InclusionInterval) → (i ·ⁱⁱ uⁱⁱ) ≡ i
·ⁱⁱ-identityʳ i = eqⁱⁱ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ⁱⁱ-identityˡ : (i : InclusionInterval) → (uⁱⁱ ·ⁱⁱ i) ≡ i
·ⁱⁱ-identityˡ i = eqⁱⁱ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ⁱⁱ-assoc : (i₁ i₂ i₃ : InclusionInterval)
          → ((i₁ ·ⁱⁱ i₂) ·ⁱⁱ i₃) ≡ (i₁ ·ⁱⁱ (i₂ ·ⁱⁱ i₃))
·ⁱⁱ-assoc i₁ i₂ i₃ =
  eqⁱⁱ (·-assoc (lo i₁) (lo i₂) (lo i₃))
       (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: the floor drops, the cap rises

infix 5 _≾ⁱⁱ_

_≾ⁱⁱ_ : InclusionInterval → InclusionInterval → Set
i₁ ≾ⁱⁱ i₂ = (lo i₁ ≾ˡᵒ lo i₂) × (hi i₁ ≾ʰⁱ hi i₂)

≾ⁱⁱ-refl : {i : InclusionInterval} → i ≾ⁱⁱ i
≾ⁱⁱ-refl {i} = ⊑-refl {traces (lo i)} , ⊑-refl {traces (hi i)}

≾ⁱⁱ-trans : {i₁ i₂ i₃ : InclusionInterval} → i₁ ≾ⁱⁱ i₂ → i₂ ≾ⁱⁱ i₃ → i₁ ≾ⁱⁱ i₃
≾ⁱⁱ-trans {i₁} {i₂} {i₃} (l₁ , h₁) (l₂ , h₂) =
    ⊑-trans {traces (lo i₃)} {traces (lo i₂)} {traces (lo i₁)} l₂ l₁
  , ⊑-trans {traces (hi i₁)} {traces (hi i₂)} {traces (hi i₃)} h₁ h₂

-- the product is monotone endpoint by endpoint

·ⁱⁱ-monoˡ : {c i₁ i₂ : InclusionInterval} → i₁ ≾ⁱⁱ i₂ → (i₁ ·ⁱⁱ c) ≾ⁱⁱ (i₂ ·ⁱⁱ c)
·ⁱⁱ-monoˡ {c} {i₁} {i₂} (l , h) =
    ⊑-·ˢ {traces (lo i₂)} {traces (lo i₁)} {traces (lo c)} {traces (lo c)}
         l (⊑-refl {traces (lo c)})
  , ⊑-·ˢ {traces (hi i₁)} {traces (hi i₂)} {traces (hi c)} {traces (hi c)}
         h (⊑-refl {traces (hi c)})

·ⁱⁱ-monoʳ : {c i₁ i₂ : InclusionInterval} → i₁ ≾ⁱⁱ i₂ → (c ·ⁱⁱ i₁) ≾ⁱⁱ (c ·ⁱⁱ i₂)
·ⁱⁱ-monoʳ {c} {i₁} {i₂} (l , h) =
    ⊑-·ˢ {traces (lo c)} {traces (lo c)} {traces (lo i₂)} {traces (lo i₁)}
         (⊑-refl {traces (lo c)}) l
  , ⊑-·ˢ {traces (hi c)} {traces (hi c)} {traces (hi i₁)} {traces (hi i₂)}
         (⊑-refl {traces (hi c)}) h

------------------------------------------------------------------------
-- Zero-product property
--
-- Both endpoints say something at the unit, unlike in
-- `LowerLift.TwoSided` where the floor half is vacuous: the floor asks
-- that the instantaneous run be required, the cap that nothing else be
-- permitted. The trace monoid being conical, each descends to the two
-- factors of a product.

≾ⁱⁱ-zero-productˡ : {i₁ i₂ : InclusionInterval}
                  → (i₁ ·ⁱⁱ i₂) ≾ⁱⁱ uⁱⁱ → i₁ ≾ⁱⁱ uⁱⁱ
≾ⁱⁱ-zero-productˡ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productˡ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productˡ {hi i₁} {hi i₂} h

≾ⁱⁱ-zero-productʳ : {i₁ i₂ : InclusionInterval}
                  → (i₁ ·ⁱⁱ i₂) ≾ⁱⁱ uⁱⁱ → i₂ ≾ⁱⁱ uⁱⁱ
≾ⁱⁱ-zero-productʳ {i₁} {i₂} (l , h) =
    ≾ˡᵒ-zero-productʳ {lo i₁} {lo i₂} l
  , ≾ʰⁱ-zero-productʳ {hi i₁} {hi i₂} h

-- both halves are decided, so the order is proof-irrelevant

≾ⁱⁱ-irrelevant : {i₁ i₂ : InclusionInterval} → (p q : i₁ ≾ⁱⁱ i₂) → p ≡ q
≾ⁱⁱ-irrelevant {i₁} {i₂} (l , h) (l' , h') =
  cong₂ _,_ (liftˢ-irrelevant l l') (liftˢ-irrelevant h h')

-- decidable equality, endpoint by endpoint

_≟ⁱⁱ_ : Decidable (_≡_ {A = InclusionInterval})
i₁ ≟ⁱⁱ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqⁱⁱ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers
--
-- `n` time steps is the singleton interval at the pure delay `⟨ n ⟩`.

of-natⁱⁱ : ℕ → InclusionInterval
of-natⁱⁱ n = [ of-nat n , of-nat n , ⊑-refl {traces (of-nat n)} ]

------------------------------------------------------------------------
-- The order is decidable, endpoint by endpoint

infix 5 _≾ⁱⁱ?_

_≾ⁱⁱ?_ : (i₁ i₂ : InclusionInterval) → Dec (i₁ ≾ⁱⁱ i₂)
i₁ ≾ⁱⁱ? i₂ = (lo i₁ ≾ˡᵒ? lo i₂) ×-dec (hi i₁ ≾ʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of two-sided inclusion intervals

inclusion-two-sided : Grade
inclusion-two-sided = record
  { Carrier         = InclusionInterval
  ; _·_             = _·ⁱⁱ_
  ; u               = uⁱⁱ
  ; ·-identityʳ     = ·ⁱⁱ-identityʳ
  ; ·-identityˡ     = ·ⁱⁱ-identityˡ
  ; ·-assoc         = ·ⁱⁱ-assoc
  ; _≾_             = _≾ⁱⁱ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ⁱⁱ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ⁱⁱ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ⁱⁱ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ⁱⁱ-trans {i} {j} {k}
  ; _≡?_            = _≟ⁱⁱ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ⁱⁱ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ⁱⁱ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ⁱⁱ-irrelevant {c} {d}
  ; of-nat          = of-natⁱⁱ
  ; of-nat-zero     = eqⁱⁱ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqⁱⁱ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }
