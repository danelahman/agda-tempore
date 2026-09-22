------------------------------------------------------------------------
-- Two-sided (closed) intervals with a possibly-infinite right-hand    --
-- endpoint as grades.                                                 --
--                                                                     --
-- As for the all-finite two-sided intervals, a grade `[ min , max ]`   --
-- bounds the elapsed time from both sides, except that `max` may now   --
-- be `∞`, imposing no upper bound at all. The arithmetic of the        --
-- endpoints lives in `Time.ExtendedNat` and is re-exported here.   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Time.TwoSidedWithInfinity where

open import Data.Empty using (⊥)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core

open import Syntax.Grades

open import Util.Equality

-- the endpoints are extended naturals

open import Syntax.Grades.Example.Time.ExtendedNat public

------------------------------------------------------------------------
-- Intervals with infinite max

record Interval∞ : Set₀ where
  constructor [_,_,_]
  field
    min : ℕ
    max : ℕ∞
    -- min is smaller or equal than max
    min≤max : ↑ min ≤∞ max

open Interval∞ public

-- interval addition

_·ᵢ_ : Interval∞ → Interval∞ → Interval∞
i₁ ·ᵢ i₂ =
  [ min i₁ + min i₂
  , max i₁ +∞ max i₂
  , +∞-mono-≤∞ {↑ min i₁} {↑ min i₂} {max i₁} {max i₂} (min≤max i₁) (min≤max i₂)
  ]

infixl 7 _·ᵢ_

-- interval unit

uᵢ : Interval∞
uᵢ = [ 0 , ↑ 0 , z≤n ]

-- interval equality

eqᵢ : ∀ {i₁ i₂}
    → min i₁ ≡ min i₂
    → max i₁ ≡ max i₂
    -----------------
    → i₁ ≡ i₂

eqᵢ {_} {i₂} refl refl =
  cong (λ x → [ min i₂ , max i₂ , x ]) (≤∞-irrelevant _ _)

-- right and left identity

·ᵢ-identityʳ : (i : Interval∞) → (i ·ᵢ uᵢ) ≡ i
·ᵢ-identityʳ i =
  eqᵢ (+-identityʳ (min i)) (+∞-identityʳ (max i))

·ᵢ-identityˡ : (i : Interval∞) → (uᵢ ·ᵢ i) ≡ i
·ᵢ-identityˡ i =
  eqᵢ (+-identityˡ (min i)) (+∞-identityˡ (max i))

-- _·ᵢ_ is associative

·ᵢ-assoc : (i₁ i₂ i₃ : Interval∞) → (i₁ ·ᵢ i₂) ·ᵢ i₃ ≡ i₁ ·ᵢ (i₂ ·ᵢ i₃)
·ᵢ-assoc i₁ i₂ i₃ =
  eqᵢ
    (+-assoc (min i₁) (min i₂) (min i₃))
    (+∞-assoc (max i₁) (max i₂) (max i₃))

-- interval order

_≾ᵢ_ : Rel Interval∞ lzero
i₁ ≾ᵢ i₂ =
  (min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂)

-- the greatest grade: no lower bound and no upper bound. It is not
-- absorbing, `⊤ᵢ ·ᵢ i` keeping `min i`.

⊤ᵢ : Interval∞
⊤ᵢ = [ 0 , ∞ , ≤∞-∞ (↑ 0) ]

≾ᵢ-⊤ : (i : Interval∞) → (min ⊤ᵢ ≤ min i × max i ≤∞ max ⊤ᵢ)
≾ᵢ-⊤ i = z≤n , ≤∞-∞ (max i)

-- uᵢ is the minimal element

uᵢ-minimal : ∀ {i} → i ≾ᵢ uᵢ → i ≡ uᵢ
uᵢ-minimal {i} (_ , maxrel) =
  eqᵢ {i} {uᵢ}
    (n≤0⇒n≡0 (≤∞-trans {↑ min i} (min≤max i) maxrel))
    (≤∞-↑0 maxrel)

-- monotonicity

·ᵢ-monoʳ-≾ᵢ : ∀ {i} → _·ᵢ_ i Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoʳ-≤ (min i) {min i₂} {min i₁} minrel ,
  +∞-mono-≤∞ {max i} {max i₁} {max i} {max i₂} (≤∞-refl {max i}) maxrel

·ᵢ-monoˡ-≾ᵢ : ∀ {i} → (_·ᵢ i) Preserves _≾ᵢ_ ⟶ _≾ᵢ_
·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} (minrel , maxrel) =
  +-monoˡ-≤ (min i) {min i₂} {min i₁} minrel ,
  +∞-mono-≤∞ {max i₁} {max i} {max i₂} {max i} maxrel (≤∞-refl {max i})

-- antisymmetry: both endpoints are pinned, and `eqᵢ` discharges the
-- `min≤max` field

≾ᵢ-antisym : {i₁ i₂ : Interval∞} → i₁ ≾ᵢ i₂ → i₂ ≾ᵢ i₁ → i₁ ≡ i₂
≾ᵢ-antisym {i₁} {i₂} (min₂≤min₁ , max₁≤max₂) (min₁≤min₂ , max₂≤max₁) =
  eqᵢ {i₁} {i₂}
    (≤-antisym min₁≤min₂ min₂≤min₁)
    (≤∞-antisym {max i₁} {max i₂} max₁≤max₂ max₂≤max₁)

-- irrelevance

≾ᵢ-irrelevant : Irrelevant _≾ᵢ_
≾ᵢ-irrelevant (relmin , relmax) (predmin , predmax) =
  cong₂ _,_ (≤-irrelevant relmin predmin) (≤∞-irrelevant relmax predmax)

-- decidability

eqᵢ? : Decidable {lzero} {Interval∞} _≡_
eqᵢ? i₁ i₂ with min i₁ ≟ min i₂ | max i₁ ≟∞ max i₂
... | yes p | yes q = yes (eqᵢ p q)
... | yes _ | no ¬q = no  λ x → ¬q (cong max x)
... | no ¬p | _     = no  λ x → ¬p (cong min x)

-- Unlike the all-finite two-sided intervals, _·ᵢ_ is *not*
-- cancellative once ∞ is allowed.

-- zero-product property

≡ᵢ-zero-productˡ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ uᵢ → i₁ ≡ uᵢ
≡ᵢ-zero-productˡ {i₁} {i₂} eq =
   eqᵢ
     (m+n≡0⇒m≡0 (min i₁) (cong min eq))
     (+∞-≡0ˡ {max i₁} {max i₂} (cong max eq))

≡ᵢ-zero-productʳ : ∀ {i₁ i₂} → i₁ ·ᵢ i₂ ≡ uᵢ → i₂ ≡ uᵢ
≡ᵢ-zero-productʳ {i₁} {i₂} eq =
  eqᵢ
    (m+n≡0⇒n≡0 (min i₁) {min i₂} (cong min eq))
    (+∞-≡0ʳ {max i₁} {max i₂} (cong max eq))

≾ᵢ-zero-productˡ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ uᵢ → i₁ ≾ᵢ uᵢ
≾ᵢ-zero-productˡ {i₁} {i₂} (_ , maxrel) =
  z≤n , +∞-≤∞-0ˡ {max i₁} {max i₂} maxrel

≾ᵢ-zero-productʳ : ∀ {i₁ i₂} → (i₁ ·ᵢ i₂) ≾ᵢ uᵢ → i₂ ≾ᵢ uᵢ
≾ᵢ-zero-productʳ {i₁} {i₂} (_ , maxrel) =
  z≤n , +∞-≤∞-0ʳ {max i₁} {max i₂} maxrel

-- binary joins: the order is containment, so the join is the smallest
-- window containing both

_⊔ᵢ_ : Interval∞ → Interval∞ → Interval∞
i₁ ⊔ᵢ i₂ =
  [ min i₁ ⊓ min i₂
  , max i₁ ⊔∞ max i₂
  , ≤∞-trans {↑ (min i₁ ⊓ min i₂)} {↑ min i₁}
             (m⊓n≤m (min i₁) (min i₂))
             (≤∞-trans {↑ min i₁} (min≤max i₁) (⊔∞-ubˡ (max i₁) (max i₂)))
  ]

infixl 7 _⊔ᵢ_

⊔ᵢ-ubˡ : (i₁ i₂ : Interval∞) → i₁ ≾ᵢ (i₁ ⊔ᵢ i₂)
⊔ᵢ-ubˡ i₁ i₂ = m⊓n≤m (min i₁) (min i₂) , ⊔∞-ubˡ (max i₁) (max i₂)

⊔ᵢ-ubʳ : (i₁ i₂ : Interval∞) → i₂ ≾ᵢ (i₁ ⊔ᵢ i₂)
⊔ᵢ-ubʳ i₁ i₂ = m⊓n≤n (min i₁) (min i₂) , ⊔∞-ubʳ (max i₁) (max i₂)

⊔ᵢ-lub : {i₁ i₂ i₃ : Interval∞} → i₁ ≾ᵢ i₃ → i₂ ≾ᵢ i₃ → (i₁ ⊔ᵢ i₂) ≾ᵢ i₃
⊔ᵢ-lub {i₁} {i₂} {i₃} (p₁ , p₂) (q₁ , q₂) =
  ⊓-glb p₁ q₁ , ⊔∞-lub {max i₁} {max i₂} {max i₃} p₂ q₂

-- addition distributes over the join at both endpoints, so the two
-- sides are equal

·ᵢ-distribˡ-⊔ᵢ : (i₁ i₂ i₃ : Interval∞)
               → (i₁ ·ᵢ (i₂ ⊔ᵢ i₃)) ≾ᵢ ((i₁ ·ᵢ i₂) ⊔ᵢ (i₁ ·ᵢ i₃))
·ᵢ-distribˡ-⊔ᵢ i₁ i₂ i₃ =
    ≤-reflexive (sym (+-distribˡ-⊓ (min i₁) (min i₂) (min i₃)))
  , ≤∞-reflexive (+∞-distribˡ-⊔∞ (max i₁) (max i₂) (max i₃))

·ᵢ-distribʳ-⊔ᵢ : (i₁ i₂ i₃ : Interval∞)
               → ((i₂ ⊔ᵢ i₃) ·ᵢ i₁) ≾ᵢ ((i₂ ·ᵢ i₁) ⊔ᵢ (i₃ ·ᵢ i₁))
·ᵢ-distribʳ-⊔ᵢ i₁ i₂ i₃ =
    ≤-reflexive (sym (+-distribʳ-⊓ (min i₁) (min i₂) (min i₃)))
  , ≤∞-reflexive (+∞-distribʳ-⊔∞ (max i₁) (max i₂) (max i₃))

-- the grade of two-sided intervals with possibly-infinite max

two-sided-intervals-with-∞ : Grade
two-sided-intervals-with-∞ = record
  { Carrier = Interval∞
  ; _·_              = _·ᵢ_
  ; u                = uᵢ
  ; ·-identityʳ      = ·ᵢ-identityʳ
  ; ·-identityˡ      = ·ᵢ-identityˡ
  ; ·-assoc          = ·ᵢ-assoc
  ; _≾_              = _≾ᵢ_
  ; ⊤                = ⊤ᵢ
  ; ≾-⊤              = ≾ᵢ-⊤
  ; _⊔_              = _⊔ᵢ_
  ; ⊔-ubˡ            = ⊔ᵢ-ubˡ
  ; ⊔-ubʳ            = ⊔ᵢ-ubʳ
  ; ⊔-lub            = λ {i₁} {i₂} {i₃} → ⊔ᵢ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾   = ·ᵢ-distribˡ-⊔ᵢ
  ; ·-distribʳ-⊔-≾   = ·ᵢ-distribʳ-⊔ᵢ
  ; ·-monoʳ-≾        = λ {i} {i₁} {i₂} rel
                         → ·ᵢ-monoʳ-≾ᵢ {i} {i₁} {i₂} rel
  ; ·-monoˡ-≾        = λ {i} {i₁} {i₂} rel
                         → ·ᵢ-monoˡ-≾ᵢ {i} {i₁} {i₂} rel
  ; ≾-refl           = ≤-refl , ≤∞-refl
  ; ≾-trans          = λ rel₁ rel₂
                         → ≤-trans (proj₁ rel₂) (proj₁ rel₁) ,
                           ≤∞-trans (proj₂ rel₁) (proj₂ rel₂)
  ; ≾-antisym        = λ {i₁} {i₂} → ≾ᵢ-antisym {i₁} {i₂}
  ; _≡?_              = eqᵢ?
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ᵢ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ᵢ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ᵢ-irrelevant {i₁} {i₂}
  ; of-nat            = λ n → [ n , ↑ n , ≤-refl ]
  ; of-nat-zero       = eqᵢ refl refl
  ; of-nat-plus       = eqᵢ refl refl
  }

------------------------------------------------------------------------
-- The same intervals with a formal greatest grade
--
-- `[ 0 , ∞ ]` is greatest but not absorbing, its `min` endpoint being
-- the unit, so the two-sided subset intervals, whose top absorbs,
-- project here rather than into the intervals above. `no-window`
-- claims no bound at either end, and absorbs.

infix 50 window_

data Interval∞⊤ : Set where
  window_   : Interval∞ → Interval∞⊤
  no-window : Interval∞⊤

window-inj : ∀ {i j} → window i ≡ window j → i ≡ j
window-inj refl = refl

-- interval addition, with `no-window` absorbing

_·ʷ_ : Interval∞⊤ → Interval∞⊤ → Interval∞⊤
(window i) ·ʷ (window j) = window (i ·ᵢ j)
(window _) ·ʷ no-window  = no-window
no-window  ·ʷ _          = no-window

infixl 7 _·ʷ_

uʷ : Interval∞⊤
uʷ = window uᵢ

-- interval order, with `no-window` greatest

_≾ʷ_ : Rel Interval∞⊤ lzero
(window i) ≾ʷ (window j) = i ≾ᵢ j
(window _) ≾ʷ no-window  = ⊤
no-window  ≾ʷ (window _) = ⊥
no-window  ≾ʷ no-window  = ⊤

infix 6 _≾ʷ_

≾ʷ-⊤ : (i : Interval∞⊤) → i ≾ʷ no-window
≾ʷ-⊤ (window _) = tt
≾ʷ-⊤ no-window  = tt

-- identity laws

·ʷ-identityʳ : (i : Interval∞⊤) → i ·ʷ uʷ ≡ i
·ʷ-identityʳ (window i) = cong window_ (·ᵢ-identityʳ i)
·ʷ-identityʳ no-window  = refl

·ʷ-identityˡ : (i : Interval∞⊤) → uʷ ·ʷ i ≡ i
·ʷ-identityˡ (window i) = cong window_ (·ᵢ-identityˡ i)
·ʷ-identityˡ no-window  = refl

-- associativity

·ʷ-assoc : (i₁ i₂ i₃ : Interval∞⊤) → (i₁ ·ʷ i₂) ·ʷ i₃ ≡ i₁ ·ʷ (i₂ ·ʷ i₃)
·ʷ-assoc (window i₁) (window i₂) (window i₃) =
  cong window_ (·ᵢ-assoc i₁ i₂ i₃)
·ʷ-assoc (window _)  (window _)  no-window   = refl
·ʷ-assoc (window _)  no-window   (window _)  = refl
·ʷ-assoc (window _)  no-window   no-window   = refl
·ʷ-assoc no-window   _           _           = refl

-- monotonicity

·ʷ-monoʳ-≾ʷ : ∀ {i} → (i ·ʷ_) Preserves _≾ʷ_ ⟶ _≾ʷ_
·ʷ-monoʳ-≾ʷ {window i} {window j} {window k} rel =
  ·ᵢ-monoʳ-≾ᵢ {i} {j} {k} rel
·ʷ-monoʳ-≾ʷ {no-window} {window _} {window _} rel = tt
·ʷ-monoʳ-≾ʷ {window _}  {window _} {no-window} rel = tt
·ʷ-monoʳ-≾ʷ {no-window} {window _} {no-window} rel = tt
·ʷ-monoʳ-≾ʷ {_}         {no-window} {window _} ()
·ʷ-monoʳ-≾ʷ {window _}  {no-window} {no-window} rel = tt
·ʷ-monoʳ-≾ʷ {no-window} {no-window} {no-window} rel = tt

·ʷ-monoˡ-≾ʷ : ∀ {i} → (_·ʷ i) Preserves _≾ʷ_ ⟶ _≾ʷ_
·ʷ-monoˡ-≾ʷ {window i} {window j} {window k} rel =
  ·ᵢ-monoˡ-≾ᵢ {i} {j} {k} rel
·ʷ-monoˡ-≾ʷ {no-window} {window _} {window _} rel = tt
·ʷ-monoˡ-≾ʷ {window _}  {window _} {no-window} rel = tt
·ʷ-monoˡ-≾ʷ {no-window} {window _} {no-window} rel = tt
·ʷ-monoˡ-≾ʷ {_}         {no-window} {window _} ()
·ʷ-monoˡ-≾ʷ {window _}  {no-window} {no-window} rel = tt
·ʷ-monoˡ-≾ʷ {no-window} {no-window} {no-window} rel = tt

-- order properties

≾ʷ-refl : Reflexive _≾ʷ_
≾ʷ-refl {window i}  = ≤-refl , ≤∞-refl
≾ʷ-refl {no-window} = tt

≾ʷ-trans : Transitive _≾ʷ_
≾ʷ-trans {window _}  {window _}  {window _}  rel₁ rel₂ =
    ≤-trans (proj₁ rel₂) (proj₁ rel₁)
  , ≤∞-trans (proj₂ rel₁) (proj₂ rel₂)
≾ʷ-trans {window _}  {window _}  {no-window} p q = tt
≾ʷ-trans {window _}  {no-window} {window _}  p ()
≾ʷ-trans {window _}  {no-window} {no-window} p q = tt
≾ʷ-trans {no-window} {window _}  {_}         () q
≾ʷ-trans {no-window} {no-window} {window _}  p ()
≾ʷ-trans {no-window} {no-window} {no-window} p q = tt

≾ʷ-antisym : {i j : Interval∞⊤} → i ≾ʷ j → j ≾ʷ i → i ≡ j
≾ʷ-antisym {window i}  {window j}  p q = cong window_ (≾ᵢ-antisym {i} {j} p q)
≾ʷ-antisym {window _}  {no-window} p ()
≾ʷ-antisym {no-window} {window _}  () q
≾ʷ-antisym {no-window} {no-window} p q = refl

≾ʷ-irrelevant : Irrelevant _≾ʷ_
≾ʷ-irrelevant {window i}  {window j}  p  q  = ≾ᵢ-irrelevant {i} {j} p q
≾ʷ-irrelevant {window _}  {no-window} tt tt = refl
≾ʷ-irrelevant {no-window} {window _}  () q
≾ʷ-irrelevant {no-window} {no-window} tt tt = refl

-- decidability

eqʷ? : Decidable {lzero} {Interval∞⊤} _≡_
eqʷ? (window i) (window j) with eqᵢ? i j
... | yes p = yes (cong window_ p)
... | no ¬p = no (λ eq → ¬p (window-inj eq))
eqʷ? (window _) no-window  = no (λ ())
eqʷ? no-window  (window _) = no (λ ())
eqʷ? no-window  no-window  = yes refl

-- zero-product properties, `no-window` sitting above the unit and not
-- below it

≾ʷ-zero-productˡ : ∀ {i₁ i₂ : Interval∞⊤} → i₁ ·ʷ i₂ ≾ʷ uʷ → i₁ ≾ʷ uʷ
≾ʷ-zero-productˡ {window i₁} {window i₂} rel =
  ≾ᵢ-zero-productˡ {i₁} {i₂} rel
≾ʷ-zero-productˡ {window _}  {no-window} ()
≾ʷ-zero-productˡ {no-window} {_}         ()

≾ʷ-zero-productʳ : ∀ {i₁ i₂ : Interval∞⊤} → i₁ ·ʷ i₂ ≾ʷ uʷ → i₂ ≾ʷ uʷ
≾ʷ-zero-productʳ {window i₁} {window i₂} rel =
  ≾ᵢ-zero-productʳ {i₁} {i₂} rel
≾ʷ-zero-productʳ {window _}  {no-window} ()
≾ʷ-zero-productʳ {no-window} {_}         ()

-- binary joins, with `no-window` the join of anything with itself

_⊔ʷ_ : Interval∞⊤ → Interval∞⊤ → Interval∞⊤
(window i) ⊔ʷ (window j) = window (i ⊔ᵢ j)
(window _) ⊔ʷ no-window  = no-window
no-window  ⊔ʷ _          = no-window

infixl 7 _⊔ʷ_

⊔ʷ-ubˡ : (i₁ i₂ : Interval∞⊤) → i₁ ≾ʷ i₁ ⊔ʷ i₂
⊔ʷ-ubˡ (window i) (window j) = ⊔ᵢ-ubˡ i j
⊔ʷ-ubˡ (window _) no-window  = tt
⊔ʷ-ubˡ no-window  _          = tt

⊔ʷ-ubʳ : (i₁ i₂ : Interval∞⊤) → i₂ ≾ʷ i₁ ⊔ʷ i₂
⊔ʷ-ubʳ (window i) (window j) = ⊔ᵢ-ubʳ i j
⊔ʷ-ubʳ (window _) no-window  = tt
⊔ʷ-ubʳ no-window  (window _) = tt
⊔ʷ-ubʳ no-window  no-window  = tt

⊔ʷ-lub : {i₁ i₂ i₃ : Interval∞⊤} → i₁ ≾ʷ i₃ → i₂ ≾ʷ i₃ → i₁ ⊔ʷ i₂ ≾ʷ i₃
⊔ʷ-lub {window i}  {window j} {window k}  p q = ⊔ᵢ-lub {i} {j} {k} p q
⊔ʷ-lub {window _}  {window _} {no-window} p q = tt
⊔ʷ-lub {window _}  {no-window} {window _} p ()
⊔ʷ-lub {window _}  {no-window} {no-window} p q = tt
⊔ʷ-lub {no-window} {_}         {window _}  () q
⊔ʷ-lub {no-window} {_}         {no-window} p q = tt

-- addition distributes over the join, `no-window` absorbing on both
-- sides

·ʷ-distribˡ-⊔ʷ : (i₁ i₂ i₃ : Interval∞⊤)
               → i₁ ·ʷ (i₂ ⊔ʷ i₃) ≾ʷ (i₁ ·ʷ i₂) ⊔ʷ (i₁ ·ʷ i₃)
·ʷ-distribˡ-⊔ʷ (window i) (window j) (window k) = ·ᵢ-distribˡ-⊔ᵢ i j k
·ʷ-distribˡ-⊔ʷ (window _) (window _) no-window  = tt
·ʷ-distribˡ-⊔ʷ (window _) no-window  _          = tt
·ʷ-distribˡ-⊔ʷ no-window  _          _          = tt

·ʷ-distribʳ-⊔ʷ : (i₁ i₂ i₃ : Interval∞⊤)
               → (i₂ ⊔ʷ i₃) ·ʷ i₁ ≾ʷ (i₂ ·ʷ i₁) ⊔ʷ (i₃ ·ʷ i₁)
·ʷ-distribʳ-⊔ʷ (window i) (window j) (window k) = ·ᵢ-distribʳ-⊔ᵢ i j k
·ʷ-distribʳ-⊔ʷ (window _) (window _) no-window  = tt
·ʷ-distribʳ-⊔ʷ no-window  (window _) (window _) = tt
·ʷ-distribʳ-⊔ʷ no-window  (window _) no-window  = tt
·ʷ-distribʳ-⊔ʷ _          no-window  _          = tt

-- the grade of two-sided intervals with a formal greatest grade

two-sided-intervals-with-⊤ : Grade
two-sided-intervals-with-⊤ = record
  { Carrier           = Interval∞⊤
  ; _·_               = _·ʷ_
  ; u                 = uʷ
  ; ·-identityʳ       = ·ʷ-identityʳ
  ; ·-identityˡ       = ·ʷ-identityˡ
  ; ·-assoc           = ·ʷ-assoc
  ; _≾_               = _≾ʷ_
  ; ⊤                 = no-window
  ; ≾-⊤               = ≾ʷ-⊤
  ; _⊔_               = _⊔ʷ_
  ; ⊔-ubˡ             = ⊔ʷ-ubˡ
  ; ⊔-ubʳ             = ⊔ʷ-ubʳ
  ; ⊔-lub             = λ {i₁} {i₂} {i₃} → ⊔ʷ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾    = ·ʷ-distribˡ-⊔ʷ
  ; ·-distribʳ-⊔-≾    = ·ʷ-distribʳ-⊔ʷ
  ; ·-monoʳ-≾         = λ {i} {i₁} {i₂} → ·ʷ-monoʳ-≾ʷ {i} {i₁} {i₂}
  ; ·-monoˡ-≾         = λ {i} {i₁} {i₂} → ·ʷ-monoˡ-≾ʷ {i} {i₁} {i₂}
  ; ≾-refl            = λ {i} → ≾ʷ-refl {i}
  ; ≾-trans           = λ {i₁} {i₂} {i₃} → ≾ʷ-trans {i₁} {i₂} {i₃}
  ; ≾-antisym         = λ {i₁} {i₂} → ≾ʷ-antisym {i₁} {i₂}
  ; _≡?_              = eqʷ?
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ʷ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ʷ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ʷ-irrelevant {i₁} {i₂}
  ; of-nat            = λ n → window [ n , ↑ n , ≤-refl ]
  ; of-nat-zero       = cong window_ (eqᵢ refl refl)
  ; of-nat-plus       = cong window_ (eqᵢ refl refl)
  }
