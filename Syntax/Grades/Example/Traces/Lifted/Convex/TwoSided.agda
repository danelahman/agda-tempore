------------------------------------------------------------------------
-- Two-sided convex trace intervals as grades.                         --
--                                                                     --
-- A grade is a *pair* of sets of traces, `[ lo , hi ]`, bounding a run --
-- from both sides as `LowerLift.TwoSided` does, but with each endpoint --
-- compared by the convex (Egli-Milner) lift rather than the Hoare one  --
-- alone:                                                              --
--                                                                     --
--   [ L₁ , U₁ ] ≾ [ L₂ , U₂ ]   iff   L₁ ≾ L₂ in `Convex.LeftSided`   --
--                                and  U₁ ≾ U₂ in `Convex.RightSided`  --
--                                                                     --
-- so the floor may still drop and the cap may still rise, but only     --
-- between alternatives already listed: the extra Smyth half of each    --
-- endpoint stops the two sets drifting apart, exactly as it does for   --
-- the one-sided convex grades.                                        --
--                                                                     --
-- The consistency field is the convex comparison of the two endpoints, --
-- the analogue of `LowerLift.TwoSided`'s `lo≼hi` and of `min≤max`.    --
--                                                                     --
-- The order lifted is a parameter: `Traces.Subtrace`'s lenient one and --
-- `Traces.SubtraceTimed`'s time-strict one both instantiate it, under  --
-- `Example.Traces.Subtrace` and `Example.Traces.SubtraceTimed`.        --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (Decidable; DecidableEquality)

open import Util.Equality

import Syntax.Grades.Traces.Order as Order

module Syntax.Grades.Example.Traces.Lifted.Convex.TwoSided
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (O : Order.TraceOrder Op) where

open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import Syntax.Grades

open import Syntax.Grades.Traces.Sets Op
open import Syntax.Grades.Traces.OrderLift Op _≟ₒ_ O

-- each endpoint is ordered exactly as the corresponding one-sided
-- convex grade orders it

open import Syntax.Grades.Example.Traces.Lifted.Convex.LeftSided Op _≟ₒ_ O
  using () renaming (_≾_ to _≾ᶜˡᵒ_; _≾?_ to _≾ᶜˡᵒ?_;
                     ≾ᶜ-zero-productˡ to ≾ᶜˡᵒ-zero-productˡ;
                     ≾ᶜ-zero-productʳ to ≾ᶜˡᵒ-zero-productʳ)
open import Syntax.Grades.Example.Traces.Lifted.Convex.RightSided Op _≟ₒ_ O
  using () renaming (_≾_ to _≾ᶜʰⁱ_; _≾?_ to _≾ᶜʰⁱ?_;
                     ≾ᶜ-zero-productˡ to ≾ᶜʰⁱ-zero-productˡ;
                     ≾ᶜ-zero-productʳ to ≾ᶜʰⁱ-zero-productʳ)

open WithDecEq _≟ₒ_ using (_≟ᴺ_; liftˢ-irrelevant)

------------------------------------------------------------------------
-- The carrier

record ConvexInterval : Set where
  constructor [_,_,_]
  field
    lo : NeTraces
    hi : NeTraces
    -- the floor sits convexly inside the cap
    lo≈hi : (traces lo ≼ˢ traces hi) × (traces lo ≽ˢ traces hi)

open ConvexInterval public

-- two intervals are equal as soon as their endpoints are: both halves
-- of the consistency witness are `True`-of-a-decision, hence irrelevant

lo≈hi-irr : {L U : NeTraces}
          → (p q : (traces L ≼ˢ traces U) × (traces L ≽ˢ traces U)) → p ≡ q
lo≈hi-irr (h , s) (h' , s') =
  cong₂ _,_ (liftˢ-irrelevant h h') (liftˢ-irrelevant s s')

eqᶜⁱ : {i₁ i₂ : ConvexInterval} → lo i₁ ≡ lo i₂ → hi i₁ ≡ hi i₂ → i₁ ≡ i₂
eqᶜⁱ {[ L , U , p ]} {[ .L , .U , q ]} refl refl =
  cong [ L , U ,_] (lo≈hi-irr {L} {U} p q)

------------------------------------------------------------------------
-- The monoid: the language product on each endpoint

infixl 7 _·ᶜⁱ_

_·ᶜⁱ_ : ConvexInterval → ConvexInterval → ConvexInterval
i₁ ·ᶜⁱ i₂ =
  [ lo i₁ · lo i₂
  , hi i₁ · hi i₂
  , ( ≼ˢ-·ˢ {traces (lo i₁)} {traces (hi i₁)} {traces (lo i₂)} {traces (hi i₂)}
            (proj₁ (lo≈hi i₁)) (proj₁ (lo≈hi i₂))
    , ≽ˢ-·ˢ {traces (lo i₁)} {traces (hi i₁)} {traces (lo i₂)} {traces (hi i₂)}
            (proj₂ (lo≈hi i₁)) (proj₂ (lo≈hi i₂)) )
  ]

uᶜⁱ : ConvexInterval
uᶜⁱ = [ u , u , (≼ˢ-refl {traces u} , ≽ˢ-refl {traces u}) ]

·ᶜⁱ-identityʳ : (i : ConvexInterval) → (i ·ᶜⁱ uᶜⁱ) ≡ i
·ᶜⁱ-identityʳ i = eqᶜⁱ (·-identityʳ (lo i)) (·-identityʳ (hi i))

·ᶜⁱ-identityˡ : (i : ConvexInterval) → (uᶜⁱ ·ᶜⁱ i) ≡ i
·ᶜⁱ-identityˡ i = eqᶜⁱ (·-identityˡ (lo i)) (·-identityˡ (hi i))

·ᶜⁱ-assoc : (i₁ i₂ i₃ : ConvexInterval)
          → ((i₁ ·ᶜⁱ i₂) ·ᶜⁱ i₃) ≡ (i₁ ·ᶜⁱ (i₂ ·ᶜⁱ i₃))
·ᶜⁱ-assoc i₁ i₂ i₃ =
  eqᶜⁱ (·-assoc (lo i₁) (lo i₂) (lo i₃))
       (·-assoc (hi i₁) (hi i₂) (hi i₃))

------------------------------------------------------------------------
-- The order: the floor drops, the cap rises, both convexly

infix 5 _≾ᶜⁱ_

_≾ᶜⁱ_ : ConvexInterval → ConvexInterval → Set
i₁ ≾ᶜⁱ i₂ = (lo i₁ ≾ᶜˡᵒ lo i₂) × (hi i₁ ≾ᶜʰⁱ hi i₂)

≾ᶜⁱ-refl : {i : ConvexInterval} → i ≾ᶜⁱ i
≾ᶜⁱ-refl {i} =
    (≼ˢ-refl {traces (lo i)} , ≽ˢ-refl {traces (lo i)})
  , (≼ˢ-refl {traces (hi i)} , ≽ˢ-refl {traces (hi i)})

≾ᶜⁱ-trans : {i₁ i₂ i₃ : ConvexInterval} → i₁ ≾ᶜⁱ i₂ → i₂ ≾ᶜⁱ i₃ → i₁ ≾ᶜⁱ i₃
≾ᶜⁱ-trans {i₁} {i₂} {i₃} ((lh₁ , ls₁) , (hh₁ , hs₁)) ((lh₂ , ls₂) , (hh₂ , hs₂)) =
    ( ≼ˢ-trans {traces (lo i₃)} {traces (lo i₂)} {traces (lo i₁)} lh₂ lh₁
    , ≽ˢ-trans {traces (lo i₃)} {traces (lo i₂)} {traces (lo i₁)} ls₂ ls₁ )
  , ( ≼ˢ-trans {traces (hi i₁)} {traces (hi i₂)} {traces (hi i₃)} hh₁ hh₂
    , ≽ˢ-trans {traces (hi i₁)} {traces (hi i₂)} {traces (hi i₃)} hs₁ hs₂ )

-- the product is monotone endpoint by endpoint, half by half

·ᶜⁱ-monoˡ : {c i₁ i₂ : ConvexInterval} → i₁ ≾ᶜⁱ i₂ → (i₁ ·ᶜⁱ c) ≾ᶜⁱ (i₂ ·ᶜⁱ c)
·ᶜⁱ-monoˡ {c} {i₁} {i₂} ((lh , ls) , (hh , hs)) =
    ( ≼ˢ-·ˢ {traces (lo i₂)} {traces (lo i₁)} {traces (lo c)} {traces (lo c)}
            lh (≼ˢ-refl {traces (lo c)})
    , ≽ˢ-·ˢ {traces (lo i₂)} {traces (lo i₁)} {traces (lo c)} {traces (lo c)}
            ls (≽ˢ-refl {traces (lo c)}) )
  , ( ≼ˢ-·ˢ {traces (hi i₁)} {traces (hi i₂)} {traces (hi c)} {traces (hi c)}
            hh (≼ˢ-refl {traces (hi c)})
    , ≽ˢ-·ˢ {traces (hi i₁)} {traces (hi i₂)} {traces (hi c)} {traces (hi c)}
            hs (≽ˢ-refl {traces (hi c)}) )

·ᶜⁱ-monoʳ : {c i₁ i₂ : ConvexInterval} → i₁ ≾ᶜⁱ i₂ → (c ·ᶜⁱ i₁) ≾ᶜⁱ (c ·ᶜⁱ i₂)
·ᶜⁱ-monoʳ {c} {i₁} {i₂} ((lh , ls) , (hh , hs)) =
    ( ≼ˢ-·ˢ {traces (lo c)} {traces (lo c)} {traces (lo i₂)} {traces (lo i₁)}
            (≼ˢ-refl {traces (lo c)}) lh
    , ≽ˢ-·ˢ {traces (lo c)} {traces (lo c)} {traces (lo i₂)} {traces (lo i₁)}
            (≽ˢ-refl {traces (lo c)}) ls )
  , ( ≼ˢ-·ˢ {traces (hi c)} {traces (hi c)} {traces (hi i₁)} {traces (hi i₂)}
            (≼ˢ-refl {traces (hi c)}) hh
    , ≽ˢ-·ˢ {traces (hi c)} {traces (hi c)} {traces (hi i₁)} {traces (hi i₂)}
            (≽ˢ-refl {traces (hi c)}) hs )

------------------------------------------------------------------------
-- Zero-product property
--
-- The floor half is vacuous, as it is in `Convex.LeftSided`; the cap
-- half is `Convex.RightSided`'s, where both of its conjuncts say
-- something at the unit.

≾ᶜⁱ-zero-productˡ : {i₁ i₂ : ConvexInterval} → (i₁ ·ᶜⁱ i₂) ≾ᶜⁱ uᶜⁱ → i₁ ≾ᶜⁱ uᶜⁱ
≾ᶜⁱ-zero-productˡ {i₁} {i₂} (l , h) =
    ≾ᶜˡᵒ-zero-productˡ {lo i₁} {lo i₂} l
  , ≾ᶜʰⁱ-zero-productˡ {hi i₁} {hi i₂} h

≾ᶜⁱ-zero-productʳ : {i₁ i₂ : ConvexInterval} → (i₁ ·ᶜⁱ i₂) ≾ᶜⁱ uᶜⁱ → i₂ ≾ᶜⁱ uᶜⁱ
≾ᶜⁱ-zero-productʳ {i₁} {i₂} (l , h) =
    ≾ᶜˡᵒ-zero-productʳ {lo i₁} {lo i₂} l
  , ≾ᶜʰⁱ-zero-productʳ {hi i₁} {hi i₂} h

-- every half is decided, so the order is proof-irrelevant

≾ᶜⁱ-irrelevant : {i₁ i₂ : ConvexInterval} → (p q : i₁ ≾ᶜⁱ i₂) → p ≡ q
≾ᶜⁱ-irrelevant {i₁} {i₂} ((lh , ls) , (hh , hs)) ((lh' , ls') , (hh' , hs')) =
  cong₂ _,_
    (cong₂ _,_ (liftˢ-irrelevant lh lh') (liftˢ-irrelevant ls ls'))
    (cong₂ _,_ (liftˢ-irrelevant hh hh') (liftˢ-irrelevant hs hs'))

-- decidable equality, endpoint by endpoint

_≟ᶜⁱ_ : Decidable (_≡_ {A = ConvexInterval})
i₁ ≟ᶜⁱ i₂ with lo i₁ ≟ᴺ lo i₂ | hi i₁ ≟ᴺ hi i₂
... | yes p | yes q = yes (eqᶜⁱ p q)
... | yes _ | no ¬q = no λ eq → ¬q (cong hi eq)
... | no ¬p | _     = no λ eq → ¬p (cong lo eq)

------------------------------------------------------------------------
-- Including the natural numbers
--
-- `n` time steps is the singleton interval at the pure delay `⟨ n ⟩`.

of-natᶜⁱ : ℕ → ConvexInterval
of-natᶜⁱ n =
  [ of-nat n , of-nat n
  , (≼ˢ-refl {traces (of-nat n)} , ≽ˢ-refl {traces (of-nat n)}) ]

------------------------------------------------------------------------
-- The order is decidable, endpoint by endpoint

infix 5 _≾ᶜⁱ?_

_≾ᶜⁱ?_ : (i₁ i₂ : ConvexInterval) → Dec (i₁ ≾ᶜⁱ i₂)
i₁ ≾ᶜⁱ? i₂ = (lo i₁ ≾ᶜˡᵒ? lo i₂) ×-dec (hi i₁ ≾ᶜʰⁱ? hi i₂)

------------------------------------------------------------------------
-- The grade of two-sided convex trace intervals

convex-two-sided : Grade
convex-two-sided = record
  { Carrier         = ConvexInterval
  ; _·_             = _·ᶜⁱ_
  ; u               = uᶜⁱ
  ; ·-identityʳ     = ·ᶜⁱ-identityʳ
  ; ·-identityˡ     = ·ᶜⁱ-identityˡ
  ; ·-assoc         = ·ᶜⁱ-assoc
  ; _≾_             = _≾ᶜⁱ_
  ; ·-monoˡ-≾       = λ {c} {x} {y} → ·ᶜⁱ-monoˡ {c} {x} {y}
  ; ·-monoʳ-≾       = λ {c} {x} {y} → ·ᶜⁱ-monoʳ {c} {x} {y}
  ; ≾-refl          = λ {x} → ≾ᶜⁱ-refl {x}
  ; ≾-trans         = λ {i} {j} {k} → ≾ᶜⁱ-trans {i} {j} {k}
  ; _≡?_            = _≟ᶜⁱ_
  ; ≾-zero-productˡ = λ {c} {d} → ≾ᶜⁱ-zero-productˡ {c} {d}
  ; ≾-zero-productʳ = λ {c} {d} → ≾ᶜⁱ-zero-productʳ {c} {d}
  ; ≾-irrelevant    = λ {c} {d} → ≾ᶜⁱ-irrelevant {c} {d}
  ; of-nat          = of-natᶜⁱ
  ; of-nat-zero     = eqᶜⁱ of-nat-zero of-nat-zero
  ; of-nat-plus     = λ {m} {n} → eqᶜⁱ (of-nat-plus {m} {n}) (of-nat-plus {m} {n})
  }
