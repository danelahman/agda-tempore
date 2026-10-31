------------------------------------------------------------------------
-- Two-sided (closed) intervals with a possibly infinite right-hand   --
-- endpoint as grades.                                                --
--                                                                    --
-- A grade `[ min , max ]` bounds the elapsed time from both sides,   --
-- "between `min` and `max` time steps", where `max` may be `∞`,      --
-- imposing no upper bound. The arithmetic of the endpoints is in     --
-- `Time.ExtendedNat` and is re-exported here.                        --
------------------------------------------------------------------------

module Grades.Examples.Time.TwoSidedWithInfinity where

open import Data.Bool.Properties using (T-irrelevant)
open import Data.Empty using (⊥)
open import Data.Nat
import Data.Nat as ℕ
open import Data.Nat.Properties
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Level renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation.Core using (¬_)

open import Data.Maybe.Base using (just; nothing)

open import Grades.Durations.Nat using (ℕᴰ)
open import Grades.Base
open import Grades.Hints using (GradeHints; comm-≡)

open import Util.Equality

-- the endpoints are extended naturals

open import Grades.Examples.Time.ExtendedNat public

------------------------------------------------------------------------
-- Intervals with infinite max
--
-- The side condition is the verdict of `_≤∞?_`, so at concrete
-- endpoints it reduces to `⊤` and a literal is written `[ m , n ]`.

record Interval∞ : Set₀ where
  constructor [_,_]
  field
    min : ℕ
    max : ℕ∞
    -- min is at most max
    {min≤max?} : True (↑ min ≤∞? max)

open Interval∞ public

-- Open ends are notation for the adjacent closed ones, as no time
-- passes strictly between two steps: `] n , a ]` is `[ n + 1 , a ]`,
-- `[ n , ↑ m [` is `[ n , ↑ (m ∸ 1) ]`, and `[ n , ∞ [` is `[ n , ∞ ]`.

-- the closed upper end just below an open one

adjacent : ℕ∞ → ℕ∞
adjacent (↑ m) = ↑ (m ∸ 1)
adjacent ∞     = ∞

adjacent-≤∞ : ∀ {n a} → ↑ ℕ.suc n ≤∞ a → ↑ n ≤∞ adjacent a
adjacent-≤∞ {n} {↑ m} p = ∸-monoˡ-≤ 1 p
adjacent-≤∞ {n} {∞}   _ = tt

infix 5 ]_,_] [_,_[ ]_,_[

]_,_] : (n : ℕ) (a : ℕ∞) → {True (↑ ℕ.suc n ≤∞? a)} → Interval∞
] n , a ] {p} = [ ℕ.suc n , a ] {p}

[_,_[ : (n : ℕ) (a : ℕ∞) → {True (↑ ℕ.suc n ≤∞? a)} → Interval∞
[ n , a [ {p} = [ n , adjacent a ] {fromWitness (adjacent-≤∞ {n} {a} (toWitness p))}

]_,_[ : (n : ℕ) (a : ℕ∞) → {True (↑ ℕ.suc (ℕ.suc n) ≤∞? a)} → Interval∞
] n , a [ {p} = [ ℕ.suc n , adjacent a ] {fromWitness (adjacent-≤∞ {ℕ.suc n} {a} (toWitness p))}

-- the side condition, as a proof

min≤max : (i : Interval∞) → ↑ min i ≤∞ max i
min≤max i = toWitness {a? = ↑ min i ≤∞? max i} (min≤max? i)

-- interval addition

_·ᵢ_ : Interval∞ → Interval∞ → Interval∞
i₁ ·ᵢ i₂ =
  [ min i₁ + min i₂
  , max i₁ +∞ max i₂
  ] {fromWitness (+∞-mono-≤∞ {↑ min i₁} {↑ min i₂} {max i₁} {max i₂}
                              (min≤max i₁) (min≤max i₂))}

infixl 7 _·ᵢ_

-- interval unit

uᵢ : Interval∞
uᵢ = [ 0 , ↑ 0 ]

-- interval equality

eqᵢ : ∀ {i₁ i₂}
    → min i₁ ≡ min i₂
    → max i₁ ≡ max i₂
    -----------------
    → i₁ ≡ i₂

eqᵢ {_} {i₂} refl refl =
  cong (λ x → [ min i₂ , max i₂ ] {x}) (T-irrelevant _ _)

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

-- _·ᵢ_ is commutative

·ᵢ-comm : (i₁ i₂ : Interval∞) → i₁ ·ᵢ i₂ ≡ i₂ ·ᵢ i₁
·ᵢ-comm i₁ i₂ = eqᵢ (+-comm (min i₁) (min i₂)) (+∞-comm (max i₁) (max i₂))

-- interval order

_≾ᵢ_ : Rel Interval∞ lzero
i₁ ≾ᵢ i₂ =
  (min i₂ ≤ min i₁ × max i₁ ≤∞ max i₂)

-- the greatest grade: no lower bound and no upper bound. It is not
-- absorbing, `⊤ᵢ ·ᵢ i` keeping `min i`.

⊤ᵢ : Interval∞
⊤ᵢ = [ 0 , ∞ ]

≾ᵢ-⊤ : (i : Interval∞) → (min ⊤ᵢ ≤ min i × max i ≤∞ max ⊤ᵢ)
≾ᵢ-⊤ i = z≤n , ≤∞-∞ (max i)

-- the unit is not least: `[ 1 , ↑ 1 ]` is not above it, its lower
-- bound being higher

uᵢ-not-least : ¬ Minimum _≾ᵢ_ uᵢ
uᵢ-not-least least = 1+n≰n (proj₁ (least [ 1 , ↑ 1 ]))

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
-- `min≤max?` field

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

_≾ᵢ?_ : Decidable _≾ᵢ_
i₁ ≾ᵢ? i₂ with min i₂ ≤? min i₁ | max i₁ ≤∞? max i₂
... | yes p | yes q = yes (p , q)
... | yes _ | no ¬q = no λ r → ¬q (proj₂ r)
... | no ¬p | _     = no λ r → ¬p (proj₁ r)

-- _·ᵢ_ is not cancellative, ∞ being absorbing.

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
  ] {fromWitness
       (≤∞-trans {↑ (min i₁ ⊓ min i₂)} {↑ min i₁}
                 (m⊓n≤m (min i₁) (min i₂))
                 (≤∞-trans {↑ min i₁} (min≤max i₁) (⊔∞-ubˡ (max i₁) (max i₂))))}

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

-- the closure: the same lower bound, and an upper bound that only no
-- time or the absent bound absorbs

plusᵢ : (i : Interval∞) → Plus _·ᵢ_ _≾ᵢ_ i
plusᵢ i = plus i⁺ (≤-refl , ≤∞-plus∞ (max i))
               (m≤m+n (min i) (min i) , plus∞-iter (max i))
               (λ (p₁ , p₂) (_ , q₂) → p₁ , plus∞-least p₂ q₂)
               (λ (p₁ , p₂) → p₁ , plus∞-indˡ p₂) (λ (p₁ , p₂) → p₁ , plus∞-indʳ p₂)
  where
    i⁺ : Interval∞
    i⁺ = [ min i , plus∞ (max i) ]
           {fromWitness (≤∞-trans {↑ min i} {max i} (min≤max i) (≤∞-plus∞ (max i)))}

-- the grade of two-sided intervals with possibly-infinite max

two-sided-intervals-with-∞ : Grade ℕᴰ
two-sided-intervals-with-∞ = posetᵍ record
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
  ; _≾?_              = _≾ᵢ?_
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ᵢ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ᵢ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ᵢ-irrelevant {i₁} {i₂}
  ; of-dur            = λ n → [ n , ↑ n ] {fromWitness ≤-refl}
  ; of-dur-zero       = eqᵢ refl refl
  ; of-dur-plus       = eqᵢ refl refl
  }

-- its hints

two-sided-intervals-with-∞ʰ : GradeHints two-sided-intervals-with-∞
two-sided-intervals-with-∞ʰ = record
  { u-least? = nothing
  ; ·-comm?  = just (comm-≡ two-sided-intervals-with-∞ ·ᵢ-comm)
  ; plus?    = λ i → just (plusᵢ i)
  }

------------------------------------------------------------------------
-- The same intervals with a formal greatest grade
--
-- `[ 0 , ∞ ]` is greatest but not absorbing, its `min` endpoint being
-- the unit. `no-window` claims no bound at either end and is absorbing;
-- the grades whose greatest element is absorbing project to these
-- intervals.

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

-- the unit is not least, as for the windows themselves

uʷ-not-least : ¬ Minimum _≾ʷ_ uʷ
uʷ-not-least least = 1+n≰n (proj₁ (least (window [ 1 , ↑ 1 ])))

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

-- commutativity

·ʷ-comm : (i₁ i₂ : Interval∞⊤) → i₁ ·ʷ i₂ ≡ i₂ ·ʷ i₁
·ʷ-comm (window i₁) (window i₂) = cong window_ (·ᵢ-comm i₁ i₂)
·ʷ-comm (window _)  no-window   = refl
·ʷ-comm no-window   (window _)  = refl
·ʷ-comm no-window   no-window   = refl

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

_≾ʷ?_ : Decidable _≾ʷ_
(window i) ≾ʷ? (window j) = i ≾ᵢ? j
(window _) ≾ʷ? no-window  = yes tt
no-window  ≾ʷ? (window _) = no λ ()
no-window  ≾ʷ? no-window  = yes tt

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

-- the closure: a window's closure, and the greatest grade its own

plusʷ : (i : Interval∞⊤) → Plus _·ʷ_ _≾ʷ_ i
plusʷ (window i) = plus (window Plus.c⁺ p) (Plus.≾-c⁺ p) (Plus.c⁺-iter p) least indˡ indʳ
  where
    p = plusᵢ i

    least : ∀ {v} → window i ≾ʷ v → v ·ʷ v ≾ʷ v → window Plus.c⁺ p ≾ʷ v
    least {window j} q r = Plus.c⁺-least p {j} q r
    least {no-window} q r = tt

    indˡ : ∀ {d} → window i ·ʷ d ≾ʷ d → window Plus.c⁺ p ·ʷ d ≾ʷ d
    indˡ {window j} q = Plus.⁺-indˡ p {j} q
    indˡ {no-window} q = tt

    indʳ : ∀ {d} → d ·ʷ window i ≾ʷ d → d ·ʷ window Plus.c⁺ p ≾ʷ d
    indʳ {window j} q = Plus.⁺-indʳ p {j} q
    indʳ {no-window} q = tt
plusʷ no-window = plus no-window tt tt least indˡ indʳ
  where
    least : ∀ {v} → no-window ≾ʷ v → v ·ʷ v ≾ʷ v → no-window ≾ʷ v
    least {no-window} q r = tt

    indˡ : ∀ {d} → no-window ·ʷ d ≾ʷ d → no-window ·ʷ d ≾ʷ d
    indˡ q = q

    indʳ : ∀ {d} → d ·ʷ no-window ≾ʷ d → d ·ʷ no-window ≾ʷ d
    indʳ q = q

-- the grade of two-sided intervals with a formal greatest grade

two-sided-intervals-with-⊤ : Grade ℕᴰ
two-sided-intervals-with-⊤ = posetᵍ record
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
  ; _≾?_              = _≾ʷ?_
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ʷ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ʷ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ʷ-irrelevant {i₁} {i₂}
  ; of-dur            = λ n → window [ n , ↑ n ] {fromWitness ≤-refl}
  ; of-dur-zero       = cong window_ (eqᵢ refl refl)
  ; of-dur-plus       = cong window_ (eqᵢ refl refl)
  }

-- its hints

two-sided-intervals-with-⊤ʰ : GradeHints two-sided-intervals-with-⊤
two-sided-intervals-with-⊤ʰ = record
  { u-least? = nothing
  ; ·-comm?  = just (comm-≡ two-sided-intervals-with-⊤ ·ʷ-comm)
  ; plus?    = λ i → just (plusʷ i)
  }
