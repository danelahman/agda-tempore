------------------------------------------------------------------------
-- Watermark grades: the trough, net change and peak of each resource --
-- a computation holds, such as the number of open files.             --
--                                                                    --
-- A grade of one resource is `(t , [d₁ , d₂] , h)`, relative to the  --
-- amount held at the start: the trough `t`, the lowest amount        --
-- reached; the range `[d₁ , d₂]` of the net change, the amount at    --
-- the end; and the peak `h`, the highest amount reached, with        --
--                                                                    --
--   t ≤ min(0 , d₁)    d₁ ≤ d₂    max(0 , d₂) ≤ h .                  --
--                                                                    --
-- Sequencing adds the net changes and shifts the later trough and    --
-- peak by the earlier net change:                                    --
--                                                                    --
--   (t , [d₁ , d₂] , h) · (t' , [d₁' , d₂'] , h')                    --
--    = (min(t , d₁ + t') , [d₁ + d₁' , d₂ + d₂'] , max(h , d₂ + h')) --
--                                                                    --
-- The upper side `(d₂ , h)` is a net change and its greatest prefix  --
-- (`Side`). Its product adds the net changes and shifts the later    --
-- prefix by the earlier net change, and only the pairs               --
-- `max(0 , d₂) ≤ h` are kept, with `(0 , 0)` as the unit. The lower  --
-- side is its mirror image, held negated: `(-d₁ , -t)` is a side as  --
-- well. A grade is a lower and an upper side whose ranges are        --
-- consistent, `d₁ ≤ d₂`.                                             --
--                                                                    --
-- The order is `t ≥ t'`, `d₁ ≥ d₁'`, `d₂ ≤ d₂'` and `h ≤ h'`, and    --
-- the join is the minimum or the maximum accordingly; `⊤` is         --
-- `(-∞ , (-∞ , ∞) , ∞)`. The unit `(0 , [0 , 0] , 0)` is the only    --
-- grade below the unit, which gives the zero-product law: from       --
-- `x · y ≾ 𝟏` the trough and peak of `x` are `0`, its range is       --
-- `[0 , 0]` by consistency, and so `y ≾ 𝟏`. The unit is not least,   --
-- `_·_` does not commute, and delays change no amount held. The      --
-- watermark grades are the grade of one resource indexed by the      --
-- resource names (`Grades.Indexed`).                                 --
------------------------------------------------------------------------

module Grades.Examples.Watermarks where

open import Data.Integer.Base as ℤ using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_; True; toWitness; map′)

open import Grades.Durations using (Duration)
open import Grades.Base using (Grade)
open import Grades.Indexed using (ℕ-names; module Maps)
open import Grades.Examples.Watermarks.ExtendedInteger

open import Util.Equality

------------------------------------------------------------------------
-- A side: a net change and its greatest prefix

record Side : Set where
  constructor side
  field
    net      : ℤ∞
    ext      : ℤ∞
    0≤ext   : 0∞ ≤∞ ext
    net≤ext : net ≤∞ ext

open Side public


infixl 7 _·ˢ_
infixl 6 _⊔ˢ_
infix  4 _≤ˢ_

_·ˢ_ : Side → Side → Side
s ·ˢ s' =
  side (net s +∞ net s') (ext s ⊔∞ (net s +∞ ext s'))
       (≤∞-trans (0≤ext s) (⊔∞-ubˡ (ext s) _))
       (≤∞-trans (+∞-monoʳ (net s) (net≤ext s')) (⊔∞-ubʳ (ext s) _))

𝟏ˢ : Side
𝟏ˢ = side 0∞ 0∞ ≤∞-refl ≤∞-refl

⊤ˢ : Side
⊤ˢ = side ∞ ∞ ≤∞-∞ ≤∞-∞

_⊔ˢ_ : Side → Side → Side
s ⊔ˢ s' =
  side (net s ⊔∞ net s') (ext s ⊔∞ ext s')
       (≤∞-trans (0≤ext s) (⊔∞-ubˡ (ext s) (ext s')))
       (⊔∞-mono (net≤ext s) (net≤ext s'))

record _≤ˢ_ (s s' : Side) : Set where
  constructor _,_
  field
    net-≤ : net s ≤∞ net s'
    ext-≤ : ext s ≤∞ ext s'

open _≤ˢ_ public

private
  ≤-≡ : ∀ {x y} → x ≡ y → x ≤∞ y
  ≤-≡ = ≤∞-reflexive

  ≥-≡ : ∀ {x y} → x ≡ y → y ≤∞ x
  ≥-≡ e = ≤∞-reflexive (sym e)

------------------------------------------------------------------------
-- The laws of a side

≤ˢ-refl : ∀ {s} → s ≤ˢ s
≤ˢ-refl = ≤∞-refl , ≤∞-refl

≤ˢ-trans : ∀ {s s' s''} → s ≤ˢ s' → s' ≤ˢ s'' → s ≤ˢ s''
≤ˢ-trans (p , q) (p' , q') = ≤∞-trans p p' , ≤∞-trans q q'

·ˢ-identityˡ : ∀ s → 𝟏ˢ ·ˢ s ≤ˢ s × s ≤ˢ 𝟏ˢ ·ˢ s
·ˢ-identityˡ s =
    (≤-≡ (+∞-identityˡ (net s)) , ⊔∞-lub (0≤ext s) (≤-≡ (+∞-identityˡ (ext s))))
  , (≥-≡ (+∞-identityˡ (net s)) , ≤∞-trans (≥-≡ (+∞-identityˡ (ext s))) (⊔∞-ubʳ 0∞ _))

·ˢ-identityʳ : ∀ s → s ·ˢ 𝟏ˢ ≤ˢ s × s ≤ˢ s ·ˢ 𝟏ˢ
·ˢ-identityʳ s =
    (≤-≡ (+∞-identityʳ (net s))
    , ⊔∞-lub ≤∞-refl (≤∞-trans (≤-≡ (+∞-identityʳ (net s))) (net≤ext s)))
  , (≥-≡ (+∞-identityʳ (net s)) , ⊔∞-ubˡ (ext s) _)

·ˢ-assoc : ∀ s s' s'' → (s ·ˢ s') ·ˢ s'' ≤ˢ s ·ˢ (s' ·ˢ s'')
                      × s ·ˢ (s' ·ˢ s'') ≤ˢ (s ·ˢ s') ·ˢ s''
·ˢ-assoc s s' s'' =
    ( ≤-≡ (+∞-assoc d d' d'')
    , ⊔∞-lub (⊔∞-lub (⊔∞-ubˡ h _)
                     (≤∞-trans (+∞-monoʳ d (⊔∞-ubˡ h' _)) (⊔∞-ubʳ h _)))
             (≤∞-trans (≤-≡ (+∞-assoc d d' h''))
               (≤∞-trans (+∞-monoʳ d (⊔∞-ubʳ h' _)) (⊔∞-ubʳ h _))) )
  , ( ≥-≡ (+∞-assoc d d' d'')
    , ⊔∞-lub (≤∞-trans (⊔∞-ubˡ h _) (⊔∞-ubˡ _ _))
             (≤∞-trans (+∞-distribˡ-⊔∞ d h' (d' +∞ h''))
               (⊔∞-mono (⊔∞-ubʳ h _) (≥-≡ (+∞-assoc d d' h'')))) )
  where
    d = net s ; h = ext s ; d' = net s' ; h' = ext s' ; d'' = net s'' ; h'' = ext s''

·ˢ-mono : ∀ {s₁ s₂ s₁' s₂'} → s₁ ≤ˢ s₁' → s₂ ≤ˢ s₂' → s₁ ·ˢ s₂ ≤ˢ s₁' ·ˢ s₂'
·ˢ-mono (p , q) (p' , q') = +∞-mono p p' , ⊔∞-mono q (+∞-mono p q')

⊔ˢ-ubˡ : ∀ s s' → s ≤ˢ s ⊔ˢ s'
⊔ˢ-ubˡ s s' = ⊔∞-ubˡ _ _ , ⊔∞-ubˡ _ _

⊔ˢ-ubʳ : ∀ s s' → s' ≤ˢ s ⊔ˢ s'
⊔ˢ-ubʳ s s' = ⊔∞-ubʳ _ _ , ⊔∞-ubʳ _ _

⊔ˢ-lub : ∀ {s s' s''} → s ≤ˢ s'' → s' ≤ˢ s'' → s ⊔ˢ s' ≤ˢ s''
⊔ˢ-lub (p , q) (p' , q') = ⊔∞-lub p p' , ⊔∞-lub q q'

·ˢ-distribˡ : ∀ s s' s'' → s ·ˢ (s' ⊔ˢ s'') ≤ˢ (s ·ˢ s') ⊔ˢ (s ·ˢ s'')
·ˢ-distribˡ s s' s'' =
    +∞-distribˡ-⊔∞ (net s) (net s') (net s'')
  , ⊔∞-lub (≤∞-trans (⊔∞-ubˡ (ext s) _) (⊔∞-ubˡ _ _))
           (≤∞-trans (+∞-distribˡ-⊔∞ (net s) (ext s') (ext s''))
                     (⊔∞-mono (⊔∞-ubʳ (ext s) _) (⊔∞-ubʳ (ext s) _)))

·ˢ-distribʳ : ∀ s s' s'' → (s' ⊔ˢ s'') ·ˢ s ≤ˢ (s' ·ˢ s) ⊔ˢ (s'' ·ˢ s)
·ˢ-distribʳ s s' s'' =
    +∞-distribʳ-⊔∞ (net s) (net s') (net s'')
  , ⊔∞-lub (⊔∞-mono (⊔∞-ubˡ (ext s') _) (⊔∞-ubˡ (ext s'') _))
           (≤∞-trans (+∞-distribʳ-⊔∞ (ext s) (net s') (net s''))
                     (⊔∞-mono (⊔∞-ubʳ (ext s') _) (⊔∞-ubʳ (ext s'') _)))

------------------------------------------------------------------------
-- The trough, net change and peak of one resource: a lower side, held
-- negated, and an upper side, with consistent net changes

record Watermark : Set where
  constructor watermark
  field
    lower       : Side
    upper       : Side
    consistent : 0∞ ≤∞ net lower +∞ net upper

open Watermark public


infixl 7 _·ᵂ_
infixl 6 _⊔ᵂ_
infix  4 _≾ᵂ_

_·ᵂ_ : Watermark → Watermark → Watermark
x ·ᵂ y =
  watermark (lower x ·ˢ lower y) (upper x ·ˢ upper y)
        (≤∞-trans (≥-≡ (+∞-identityˡ 0∞))
          (≤∞-trans (+∞-mono (consistent x) (consistent y))
                    (≤-≡ (shuffle (net (lower x)) (net (upper x)) (net (lower y)) (net (upper y))))))
  where
    shuffle : ∀ a b c d → (a +∞ b) +∞ (c +∞ d) ≡ (a +∞ c) +∞ (b +∞ d)
    shuffle a b c d =
      trans (+∞-assoc a b (c +∞ d))
        (trans (cong (a +∞_) (trans (sym (+∞-assoc b c d))
                               (trans (cong (_+∞ d) (+∞-comm b c)) (+∞-assoc c b d))))
               (sym (+∞-assoc a c (b +∞ d))))

𝟏ᵂ : Watermark
𝟏ᵂ = watermark 𝟏ˢ 𝟏ˢ (≤∞-reflexive (sym (+∞-identityˡ 0∞)))

⊤ᵂ : Watermark
⊤ᵂ = watermark ⊤ˢ ⊤ˢ ≤∞-∞

_⊔ᵂ_ : Watermark → Watermark → Watermark
x ⊔ᵂ y =
  watermark (lower x ⊔ˢ lower y) (upper x ⊔ˢ upper y)
        (≤∞-trans (consistent x)
          (+∞-mono (⊔∞-ubˡ (net (lower x)) _) (⊔∞-ubˡ (net (upper x)) _)))

_≾ᵂ_ : Watermark → Watermark → Set
x ≾ᵂ y = (lower x ≤ˢ lower y) × (upper x ≤ˢ upper y)

_≾ᵂ?_ : ∀ x y → Dec (x ≾ᵂ y)
x ≾ᵂ? y = side? (lower x) (lower y) ×-dec side? (upper x) (upper y)
  where
    side? : ∀ s s' → Dec (s ≤ˢ s')
    side? s s' = map′ (λ (p , q) → p , q) (λ (p , q) → p , q)
                      ((net s ≤∞? net s') ×-dec (ext s ≤∞? ext s'))

------------------------------------------------------------------------
-- The zero-product law

private
  -- the extreme of the first side of a product below the unit's
  ext-≤0 : ∀ s s' → ext (s ·ˢ s') ≤∞ 0∞ → ext s ≤∞ 0∞
  ext-≤0 s s' p = ≤∞-trans (⊔∞-ubˡ (ext s) _) p

  -- the net change of a side below 0 where its extreme is
  net-≤0 : ∀ s → ext s ≤∞ 0∞ → net s ≤∞ 0∞
  net-≤0 s p = ≤∞-trans (net≤ext s) p

  -- a net change at most 0, consistent with another at most 0, is 0
  net-≥0 : ∀ a b → a ≤∞ 0∞ → 0∞ ≤∞ a +∞ b → 0∞ ≤∞ b
  net-≥0 a b p q = ≤∞-trans q (≤∞-trans (+∞-monoˡ b p) (≤-≡ (+∞-identityˡ b)))

  -- the second side of a product below the unit's, the first one's
  -- net change being 0
  second-≤𝟏 : ∀ s s' → 0∞ ≤∞ net s → s ·ˢ s' ≤ˢ 𝟏ˢ → s' ≤ˢ 𝟏ˢ
  second-≤𝟏 s s' n (_ , e) =
      ≤∞-trans (net≤ext s') h'≤0
    , h'≤0
    where
      h'≤0 : ext s' ≤∞ 0∞
      h'≤0 = +∞-≤0ʳ n (≤∞-trans (⊔∞-ubʳ (ext s) _) e)

zero-productˡ : ∀ {x y} → x ·ᵂ y ≾ᵂ 𝟏ᵂ → x ≾ᵂ 𝟏ᵂ
zero-productˡ {x} {y} ((_ , el) , (_ , eu)) =
    (net-≤0 (lower x) (ext-≤0 (lower x) (lower y) el) , ext-≤0 (lower x) (lower y) el)
  , (net-≤0 (upper x) (ext-≤0 (upper x) (upper y) eu) , ext-≤0 (upper x) (upper y) eu)

zero-productʳ : ∀ {x y} → x ·ᵂ y ≾ᵂ 𝟏ᵂ → y ≾ᵂ 𝟏ᵂ
zero-productʳ {x} {y} p@(pl , pu) =
    second-≤𝟏 (lower x) (lower y) (net-≥0 (net (upper x)) (net (lower x)) nu cons′) pl
  , second-≤𝟏 (upper x) (upper y) (net-≥0 (net (lower x)) (net (upper x)) nl (consistent x)) pu
  where
    xu = zero-productˡ {x} {y} p
    nl = net-≤ (proj₁ xu)
    nu = net-≤ (proj₂ xu)
    cons′ = ≤∞-trans (consistent x) (≤∞-reflexive (+∞-comm (net (lower x)) (net (upper x))))

------------------------------------------------------------------------
-- The grade of one watermark: the trough, net change and peak of one
-- resource

one-watermark : {D : Duration} → Grade D
one-watermark = record
  { Carrier         = Watermark
  ; _·_             = _·ᵂ_
  ; 𝟏               = 𝟏ᵂ
  ; _≾_             = _≾ᵂ_
  ; ⊤               = ⊤ᵂ
  ; _⊔_             = _⊔ᵂ_
  ; ι               = λ _ → 𝟏ᵂ
  ; ·-identityˡ     = λ x → pair (·ˢ-identityˡ (lower x)) (·ˢ-identityˡ (upper x))
  ; ·-identityʳ     = λ x → pair (·ˢ-identityʳ (lower x)) (·ˢ-identityʳ (upper x))
  ; ·-assoc         = λ x y z → pair (·ˢ-assoc (lower x) (lower y) (lower z))
                                     (·ˢ-assoc (upper x) (upper y) (upper z))
  ; ≾-refl          = ≤ˢ-refl , ≤ˢ-refl
  ; ≾-trans         = λ (p , q) (p' , q') → ≤ˢ-trans p p' , ≤ˢ-trans q q'
  ; ≾-irrelevant    = λ ((a , b) , (c , d)) ((a' , b') , (c' , d')) →
      cong₂ _,_ (cong₂ _,_ (≤∞-irrelevant a a') (≤∞-irrelevant b b'))
                (cong₂ _,_ (≤∞-irrelevant c c') (≤∞-irrelevant d d'))
  ; _≾?_            = _≾ᵂ?_
  ; ≾-⊤             = λ x → (≤∞-∞ , ≤∞-∞) , (≤∞-∞ , ≤∞-∞)
  ; ⊔-ubˡ           = λ x y → ⊔ˢ-ubˡ (lower x) (lower y) , ⊔ˢ-ubˡ (upper x) (upper y)
  ; ⊔-ubʳ           = λ x y → ⊔ˢ-ubʳ (lower x) (lower y) , ⊔ˢ-ubʳ (upper x) (upper y)
  ; ⊔-lub           = λ (p , q) (p' , q') → ⊔ˢ-lub p p' , ⊔ˢ-lub q q'
  ; ·-monoˡ-≾       = λ {c} (p , q) → ·ˢ-mono p (≤ˢ-refl {lower c}) , ·ˢ-mono q (≤ˢ-refl {upper c})
  ; ·-monoʳ-≾       = λ {c} (p , q) → ·ˢ-mono (≤ˢ-refl {lower c}) p , ·ˢ-mono (≤ˢ-refl {upper c}) q
  ; ·-distribˡ-⊔-≾  = λ x y z → ·ˢ-distribˡ (lower x) (lower y) (lower z)
                              , ·ˢ-distribˡ (upper x) (upper y) (upper z)
  ; ·-distribʳ-⊔-≾  = λ x y z → ·ˢ-distribʳ (lower x) (lower y) (lower z)
                              , ·ˢ-distribʳ (upper x) (upper y) (upper z)
  ; ≾-zero-productˡ = λ {x} {y} → zero-productˡ {x} {y}
  ; ≾-zero-productʳ = λ {x} {y} → zero-productʳ {x} {y}
  ; ι-zero          = (≤ˢ-refl , ≤ˢ-refl) , (≤ˢ-refl , ≤ˢ-refl)
  ; ι-plus          = pair (·ˢ-identityˡ 𝟏ˢ) (·ˢ-identityˡ 𝟏ˢ) .proj₂ , pair (·ˢ-identityˡ 𝟏ˢ) (·ˢ-identityˡ 𝟏ˢ) .proj₁
  }
  where
    pair : ∀ {a b c d : Side} → a ≤ˢ b × b ≤ˢ a → c ≤ˢ d × d ≤ˢ c
         → ((a ≤ˢ b) × (c ≤ˢ d)) × ((b ≤ˢ a) × (d ≤ˢ c))
    pair (p , p') (q , q') = (p , q) , (p' , q')

------------------------------------------------------------------------
-- The watermark grades: one grade per resource name

watermarks : {D : Duration} → Grade D
watermarks {D} = Maps.indexedᵍ ℕ-names (one-watermark {D})

------------------------------------------------------------------------
-- Literals: the trough, the range of net changes and the peak, the
-- trough and the lower end of the range possibly `-∞` (given negated,
-- as an element of `ℤ∞`)

-- the side conditions, decided

Wellformed : (t̃ d̃₁ d₂ h : ℤ∞) → Set
Wellformed t̃ d̃₁ d₂ h =
  True (((0∞ ≤∞? t̃) ×-dec (d̃₁ ≤∞? t̃)) ×-dec ((0∞ ≤∞? h) ×-dec (d₂ ≤∞? h))
        ×-dec (0∞ ≤∞? d̃₁ +∞ d₂))

-- `(t , [d₁ , d₂] , h)` from `t̃ = -t` and `d̃₁ = -d₁`

watermarkⁿ : (t̃ d̃₁ d₂ h : ℤ∞) {w : Wellformed t̃ d̃₁ d₂ h} → Watermark
watermarkⁿ t̃ d̃₁ d₂ h {w} with toWitness w
... | (a , b) , ((c , d) , e) = watermark (side d̃₁ t̃ a b) (side d₂ h c d) e
