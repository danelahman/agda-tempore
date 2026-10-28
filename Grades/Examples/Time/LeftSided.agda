------------------------------------------------------------------------
-- (Left) one-sided (closed) intervals as grades.                     --
--                                                                    --
-- A grade `[ n ,+∞⟩` is a lower bound, "at least `n` time steps".    --
-- Multiplication adds the bounds and the order is the reverse of `≤` --
-- on them, and a *smaller* bound is the weaker grade.                --
------------------------------------------------------------------------

module Grades.Examples.Time.LeftSided where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; upTo) renaming (map to mapᴸ)
open import Data.Nat.ListAction using (sum)
open import Data.Nat
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

open import Util.Equality

-- type of (left) one-sided intervals

data 𝕀 : Set where
  [_,+∞⟩ : ℕ → 𝕀

-- equality helpers

eq𝕀 : ∀ {m n} → m ≡ n → [ m ,+∞⟩ ≡ [ n ,+∞⟩
eq𝕀 = cong [_,+∞⟩

𝕀-inj : ∀ {m n} → [ m ,+∞⟩ ≡ [ n ,+∞⟩ → m ≡ n
𝕀-inj refl = refl

-- interval addition

_·ₒ_ : 𝕀 → 𝕀 → 𝕀
[ m ,+∞⟩ ·ₒ [ n ,+∞⟩ = [ m + n ,+∞⟩

infixl 7 _·ₒ_

-- interval unit

uₒ : 𝕀
uₒ = [ 0 ,+∞⟩

-- interval order

_≾ₒ_ : Rel 𝕀 lzero
[ m ,+∞⟩ ≾ₒ [ n ,+∞⟩ = n ≤ m

infix 6 _≾ₒ_

-- identity laws

·ₒ-identityʳ : (i : 𝕀) → i ·ₒ uₒ ≡ i
·ₒ-identityʳ [ m ,+∞⟩ = eq𝕀 (+-identityʳ m)

·ₒ-identityˡ : (i : 𝕀) → uₒ ·ₒ i ≡ i
·ₒ-identityˡ [ m ,+∞⟩ = eq𝕀 (+-identityˡ m)

-- associativity

·ₒ-assoc : (i₁ i₂ i₃ : 𝕀) → (i₁ ·ₒ i₂) ·ₒ i₃ ≡ i₁ ·ₒ (i₂ ·ₒ i₃)
·ₒ-assoc [ m ,+∞⟩ [ n ,+∞⟩ [ o ,+∞⟩ = eq𝕀 (+-assoc m n o)

-- commutativity

·ₒ-comm : (i₁ i₂ : 𝕀) → i₁ ·ₒ i₂ ≡ i₂ ·ₒ i₁
·ₒ-comm [ m ,+∞⟩ [ n ,+∞⟩ = eq𝕀 (+-comm m n)

-- monotonicity

·ₒ-monoʳ-≾ₒ : ∀ {i} → (i ·ₒ_) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoʳ-≾ₒ {[ m ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} = +-monoʳ-≤ m

·ₒ-monoˡ-≾ₒ : ∀ {i} → (_·ₒ i) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoˡ-≾ₒ {[ m ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} = +-monoˡ-≤ m

-- order properties

≾ₒ-refl : Reflexive _≾ₒ_
≾ₒ-refl {[ _ ,+∞⟩} = ≤-refl

≾ₒ-trans : Transitive _≾ₒ_
≾ₒ-trans {[ _ ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} p q = ≤-trans q p

≾ₒ-antisym : {i j : 𝕀} → i ≾ₒ j → j ≾ₒ i → i ≡ j
≾ₒ-antisym {[ _ ,+∞⟩} {[ _ ,+∞⟩} p q = eq𝕀 (≤-antisym q p)

≾ₒ-irrelevant : Irrelevant _≾ₒ_
≾ₒ-irrelevant {[ _ ,+∞⟩} {[ _ ,+∞⟩} = ≤-irrelevant

-- the unit is the greatest grade: demanding nothing is the weakest
-- lower bound there is

≾ₒ-⊤ : (i : 𝕀) → i ≾ₒ uₒ
≾ₒ-⊤ [ _ ,+∞⟩ = z≤n

-- the unit is not least: `[ 1 ,+∞⟩` lies strictly below it

uₒ-not-least : ¬ Minimum _≾ₒ_ uₒ
uₒ-not-least least = 1+n≰n (least [ 1 ,+∞⟩)

-- decidability

_≾ₒ?_ : Decidable _≾ₒ_
[ m ,+∞⟩ ≾ₒ? [ n ,+∞⟩ = n ≤? m

-- cancellativity

·ₒ-≾ₒ-cancellativeˡ : (i₁ i₂ i₃ : 𝕀) → (i₁ ·ₒ i₂) ≾ₒ (i₁ ·ₒ i₃) → i₂ ≾ₒ i₃
·ₒ-≾ₒ-cancellativeˡ [ m₁ ,+∞⟩ [ m₂ ,+∞⟩ [ m₃ ,+∞⟩ rel =
  +-cancelˡ-≤ m₁ m₃ m₂ rel


-- zero-product properties

≡ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≡ uₒ → i₁ ≡ uₒ
≡ₒ-zero-productˡ {[ m ,+∞⟩} {[ _ ,+∞⟩} eq = eq𝕀 (m+n≡0⇒m≡0 m (𝕀-inj eq))

≡ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≡ uₒ → i₂ ≡ uₒ
≡ₒ-zero-productʳ {[ m ,+∞⟩} {[ _ ,+∞⟩} eq = eq𝕀 (m+n≡0⇒n≡0 m (𝕀-inj eq))

≾ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₁ ≾ₒ uₒ
≾ₒ-zero-productˡ {[ _ ,+∞⟩} {[ _ ,+∞⟩} _ = z≤n

≾ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≾ₒ uₒ → i₂ ≾ₒ uₒ
≾ₒ-zero-productʳ {[ _ ,+∞⟩} {[ _ ,+∞⟩} _ = z≤n

-- binary joins: a weaker grade has the smaller bound, so the join
-- takes the minimum of the two bounds

_⊔ₒ_ : 𝕀 → 𝕀 → 𝕀
[ m ,+∞⟩ ⊔ₒ [ n ,+∞⟩ = [ m ⊓ n ,+∞⟩

infixl 7 _⊔ₒ_

⊔ₒ-ubˡ : (i₁ i₂ : 𝕀) → i₁ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubˡ [ m ,+∞⟩ [ n ,+∞⟩ = m⊓n≤m m n

⊔ₒ-ubʳ : (i₁ i₂ : 𝕀) → i₂ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubʳ [ m ,+∞⟩ [ n ,+∞⟩ = m⊓n≤n m n

⊔ₒ-lub : {i₁ i₂ i₃ : 𝕀} → i₁ ≾ₒ i₃ → i₂ ≾ₒ i₃ → i₁ ⊔ₒ i₂ ≾ₒ i₃
⊔ₒ-lub {[ _ ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} p q = ⊓-glb p q

-- addition distributes over the join, so the two sides are equal

·ₒ-distribˡ-⊔ₒ : (i₁ i₂ i₃ : 𝕀) → i₁ ·ₒ (i₂ ⊔ₒ i₃) ≾ₒ (i₁ ·ₒ i₂) ⊔ₒ (i₁ ·ₒ i₃)
·ₒ-distribˡ-⊔ₒ [ m ,+∞⟩ [ n ,+∞⟩ [ o ,+∞⟩ =
  ≤-reflexive (sym (+-distribˡ-⊓ m n o))

·ₒ-distribʳ-⊔ₒ : (i₁ i₂ i₃ : 𝕀) → (i₂ ⊔ₒ i₃) ·ₒ i₁ ≾ₒ (i₂ ·ₒ i₁) ⊔ₒ (i₃ ·ₒ i₁)
·ₒ-distribʳ-⊔ₒ [ m ,+∞⟩ [ n ,+∞⟩ [ o ,+∞⟩ =
  ≤-reflexive (sym (+-distribʳ-⊓ m n o))

-- the grade of one-sided intervals

-- every grade absorbs its own iteration, and is its own closure

·ₒ-iter : (i : 𝕀) → i ·ₒ i ≾ₒ i
·ₒ-iter [ m ,+∞⟩ = m≤m+n m m

left-sided-intervals : Grade ℕᴰ
left-sided-intervals = posetᵍ record
  { Carrier          = 𝕀
  ; _·_               = _·ₒ_
  ; u                 = uₒ
  ; ·-identityʳ       = ·ₒ-identityʳ
  ; ·-identityˡ       = ·ₒ-identityˡ
  ; ·-assoc           = ·ₒ-assoc
  ; _≾_               = _≾ₒ_
  ; ⊤                 = uₒ
  ; ≾-⊤               = ≾ₒ-⊤
  ; u-least?          = nothing
  ; ·-comm?           = just ·ₒ-comm
  ; plus?             = λ i → just (plus-self (≾ₒ-refl {i}) (·ₒ-iter i))
  ; _⊔_               = _⊔ₒ_
  ; ⊔-ubˡ             = ⊔ₒ-ubˡ
  ; ⊔-ubʳ             = ⊔ₒ-ubʳ
  ; ⊔-lub             = ⊔ₒ-lub
  ; ·-distribˡ-⊔-≾    = ·ₒ-distribˡ-⊔ₒ
  ; ·-distribʳ-⊔-≾    = ·ₒ-distribʳ-⊔ₒ
  ; ·-monoʳ-≾         = ·ₒ-monoʳ-≾ₒ
  ; ·-monoˡ-≾         = ·ₒ-monoˡ-≾ₒ
  ; ≾-refl            = ≾ₒ-refl
  ; ≾-trans           = ≾ₒ-trans
  ; ≾-antisym         = λ {i} {j} → ≾ₒ-antisym {i} {j}
  ; _≾?_              = _≾ₒ?_
  ; ≾-zero-productˡ   = ≾ₒ-zero-productˡ
  ; ≾-zero-productʳ   = ≾ₒ-zero-productʳ
  ; ≾-irrelevant      = ≾ₒ-irrelevant
  ; of-dur            = [_,+∞⟩
  ; of-dur-zero       = refl
  ; of-dur-plus       = refl
  }

------------------------------------------------------------------------
-- The same intervals with a formal greatest grade
--
-- `[ 0 ,+∞⟩` is greatest but, being the unit, not absorbing. `untimed`
-- claims no lower bound and is absorbing; the grades whose greatest
-- element is absorbing project to these intervals.

infix 50 timed_

data 𝕀⊤ : Set where
  timed_  : 𝕀 → 𝕀⊤
  untimed : 𝕀⊤

timed-inj : ∀ {i j} → timed i ≡ timed j → i ≡ j
timed-inj refl = refl

-- interval addition, with `untimed` absorbing

_·ᵗ_ : 𝕀⊤ → 𝕀⊤ → 𝕀⊤
(timed i) ·ᵗ (timed j) = timed (i ·ₒ j)
(timed _) ·ᵗ untimed   = untimed
untimed   ·ᵗ _         = untimed

infixl 7 _·ᵗ_

uᵗ : 𝕀⊤
uᵗ = timed uₒ

-- interval order, with `untimed` greatest

_≾ᵗ_ : Rel 𝕀⊤ lzero
(timed i) ≾ᵗ (timed j) = i ≾ₒ j
(timed _) ≾ᵗ untimed   = ⊤
untimed   ≾ᵗ (timed _) = ⊥
untimed   ≾ᵗ untimed   = ⊤

infix 6 _≾ᵗ_

≾ᵗ-⊤ : (i : 𝕀⊤) → i ≾ᵗ untimed
≾ᵗ-⊤ (timed _) = tt
≾ᵗ-⊤ untimed   = tt

-- the unit is not least, as for the intervals themselves

uᵗ-not-least : ¬ Minimum _≾ᵗ_ uᵗ
uᵗ-not-least least = 1+n≰n (least (timed [ 1 ,+∞⟩))

-- identity laws

·ᵗ-identityʳ : (i : 𝕀⊤) → i ·ᵗ uᵗ ≡ i
·ᵗ-identityʳ (timed i) = cong timed_ (·ₒ-identityʳ i)
·ᵗ-identityʳ untimed   = refl

·ᵗ-identityˡ : (i : 𝕀⊤) → uᵗ ·ᵗ i ≡ i
·ᵗ-identityˡ (timed i) = cong timed_ (·ₒ-identityˡ i)
·ᵗ-identityˡ untimed   = refl

-- associativity

·ᵗ-assoc : (i₁ i₂ i₃ : 𝕀⊤) → (i₁ ·ᵗ i₂) ·ᵗ i₃ ≡ i₁ ·ᵗ (i₂ ·ᵗ i₃)
·ᵗ-assoc (timed i₁) (timed i₂) (timed i₃) = cong timed_ (·ₒ-assoc i₁ i₂ i₃)
·ᵗ-assoc (timed _)  (timed _)  untimed    = refl
·ᵗ-assoc (timed _)  untimed    (timed _)  = refl
·ᵗ-assoc (timed _)  untimed    untimed    = refl
·ᵗ-assoc untimed    _          _          = refl

-- commutativity

·ᵗ-comm : (i₁ i₂ : 𝕀⊤) → i₁ ·ᵗ i₂ ≡ i₂ ·ᵗ i₁
·ᵗ-comm (timed i₁) (timed i₂) = cong timed_ (·ₒ-comm i₁ i₂)
·ᵗ-comm (timed _)  untimed    = refl
·ᵗ-comm untimed    (timed _)  = refl
·ᵗ-comm untimed    untimed    = refl

-- monotonicity

·ᵗ-monoʳ-≾ᵗ : ∀ {i} → (i ·ᵗ_) Preserves _≾ᵗ_ ⟶ _≾ᵗ_
·ᵗ-monoʳ-≾ᵗ {timed i} {timed j} {timed k} rel = ·ₒ-monoʳ-≾ₒ {i} {j} {k} rel
·ᵗ-monoʳ-≾ᵗ {untimed} {timed _} {timed _} rel = tt
·ᵗ-monoʳ-≾ᵗ {timed _} {timed _} {untimed} rel = tt
·ᵗ-monoʳ-≾ᵗ {untimed} {timed _} {untimed} rel = tt
·ᵗ-monoʳ-≾ᵗ {_}       {untimed} {timed _} ()
·ᵗ-monoʳ-≾ᵗ {timed _} {untimed} {untimed} rel = tt
·ᵗ-monoʳ-≾ᵗ {untimed} {untimed} {untimed} rel = tt

·ᵗ-monoˡ-≾ᵗ : ∀ {i} → (_·ᵗ i) Preserves _≾ᵗ_ ⟶ _≾ᵗ_
·ᵗ-monoˡ-≾ᵗ {timed i} {timed j} {timed k} rel = ·ₒ-monoˡ-≾ₒ {i} {j} {k} rel
·ᵗ-monoˡ-≾ᵗ {untimed} {timed _} {timed _} rel = tt
·ᵗ-monoˡ-≾ᵗ {timed _} {timed _} {untimed} rel = tt
·ᵗ-monoˡ-≾ᵗ {untimed} {timed _} {untimed} rel = tt
·ᵗ-monoˡ-≾ᵗ {_}       {untimed} {timed _} ()
·ᵗ-monoˡ-≾ᵗ {timed _} {untimed} {untimed} rel = tt
·ᵗ-monoˡ-≾ᵗ {untimed} {untimed} {untimed} rel = tt

-- order properties

≾ᵗ-refl : Reflexive _≾ᵗ_
≾ᵗ-refl {timed i} = ≾ₒ-refl {i}
≾ᵗ-refl {untimed} = tt

≾ᵗ-trans : Transitive _≾ᵗ_
≾ᵗ-trans {timed i}  {timed j}  {timed k}  p q = ≾ₒ-trans {i} {j} {k} p q
≾ᵗ-trans {timed _}  {timed _}  {untimed}  p q = tt
≾ᵗ-trans {timed _}  {untimed}  {timed _}  p ()
≾ᵗ-trans {timed _}  {untimed}  {untimed}  p q = tt
≾ᵗ-trans {untimed}  {timed _}  {_}        () q
≾ᵗ-trans {untimed}  {untimed}  {timed _}  p ()
≾ᵗ-trans {untimed}  {untimed}  {untimed}  p q = tt

≾ᵗ-antisym : {i j : 𝕀⊤} → i ≾ᵗ j → j ≾ᵗ i → i ≡ j
≾ᵗ-antisym {timed i} {timed j} p q = cong timed_ (≾ₒ-antisym {i} {j} p q)
≾ᵗ-antisym {timed _} {untimed} p ()
≾ᵗ-antisym {untimed} {timed _} () q
≾ᵗ-antisym {untimed} {untimed} p q = refl

≾ᵗ-irrelevant : Irrelevant _≾ᵗ_
≾ᵗ-irrelevant {timed i} {timed j} p  q  = ≾ₒ-irrelevant {i} {j} p q
≾ᵗ-irrelevant {timed _} {untimed} tt tt = refl
≾ᵗ-irrelevant {untimed} {timed _} () q
≾ᵗ-irrelevant {untimed} {untimed} tt tt = refl

-- decidability

_≾ᵗ?_ : Decidable _≾ᵗ_
(timed i) ≾ᵗ? (timed j) = i ≾ₒ? j
(timed _) ≾ᵗ? untimed   = yes tt
untimed   ≾ᵗ? (timed _) = no λ ()
untimed   ≾ᵗ? untimed   = yes tt

-- zero-product properties, `untimed` sitting above the unit and not
-- below it

≾ᵗ-zero-productˡ : ∀ {i₁ i₂ : 𝕀⊤} → i₁ ·ᵗ i₂ ≾ᵗ uᵗ → i₁ ≾ᵗ uᵗ
≾ᵗ-zero-productˡ {timed i₁} {timed i₂} rel = ≾ₒ-zero-productˡ {i₁} {i₂} rel
≾ᵗ-zero-productˡ {timed _}  {untimed}  ()
≾ᵗ-zero-productˡ {untimed}  {_}        ()

≾ᵗ-zero-productʳ : ∀ {i₁ i₂ : 𝕀⊤} → i₁ ·ᵗ i₂ ≾ᵗ uᵗ → i₂ ≾ᵗ uᵗ
≾ᵗ-zero-productʳ {timed i₁} {timed i₂} rel = ≾ₒ-zero-productʳ {i₁} {i₂} rel
≾ᵗ-zero-productʳ {timed _}  {untimed}  ()
≾ᵗ-zero-productʳ {untimed}  {_}        ()

-- binary joins, with `untimed` the join of anything with itself

_⊔ᵗ_ : 𝕀⊤ → 𝕀⊤ → 𝕀⊤
(timed i) ⊔ᵗ (timed j) = timed (i ⊔ₒ j)
(timed _) ⊔ᵗ untimed   = untimed
untimed   ⊔ᵗ _         = untimed

infixl 7 _⊔ᵗ_

⊔ᵗ-ubˡ : (i₁ i₂ : 𝕀⊤) → i₁ ≾ᵗ i₁ ⊔ᵗ i₂
⊔ᵗ-ubˡ (timed i) (timed j) = ⊔ₒ-ubˡ i j
⊔ᵗ-ubˡ (timed _) untimed   = tt
⊔ᵗ-ubˡ untimed   _         = tt

⊔ᵗ-ubʳ : (i₁ i₂ : 𝕀⊤) → i₂ ≾ᵗ i₁ ⊔ᵗ i₂
⊔ᵗ-ubʳ (timed i) (timed j) = ⊔ₒ-ubʳ i j
⊔ᵗ-ubʳ (timed _) untimed   = tt
⊔ᵗ-ubʳ untimed   (timed _) = tt
⊔ᵗ-ubʳ untimed   untimed   = tt

⊔ᵗ-lub : {i₁ i₂ i₃ : 𝕀⊤} → i₁ ≾ᵗ i₃ → i₂ ≾ᵗ i₃ → i₁ ⊔ᵗ i₂ ≾ᵗ i₃
⊔ᵗ-lub {timed i} {timed j} {timed k} p q = ⊔ₒ-lub {i} {j} {k} p q
⊔ᵗ-lub {timed _} {timed _} {untimed} p q = tt
⊔ᵗ-lub {timed _} {untimed} {timed _} p ()
⊔ᵗ-lub {timed _} {untimed} {untimed} p q = tt
⊔ᵗ-lub {untimed} {_}       {timed _} () q
⊔ᵗ-lub {untimed} {_}       {untimed} p q = tt

-- addition distributes over the join, `untimed` absorbing on both sides

·ᵗ-distribˡ-⊔ᵗ : (i₁ i₂ i₃ : 𝕀⊤) → i₁ ·ᵗ (i₂ ⊔ᵗ i₃) ≾ᵗ (i₁ ·ᵗ i₂) ⊔ᵗ (i₁ ·ᵗ i₃)
·ᵗ-distribˡ-⊔ᵗ (timed i) (timed j) (timed k) = ·ₒ-distribˡ-⊔ₒ i j k
·ᵗ-distribˡ-⊔ᵗ (timed _) (timed _) untimed   = tt
·ᵗ-distribˡ-⊔ᵗ (timed _) untimed   _         = tt
·ᵗ-distribˡ-⊔ᵗ untimed   _         _         = tt

·ᵗ-distribʳ-⊔ᵗ : (i₁ i₂ i₃ : 𝕀⊤) → (i₂ ⊔ᵗ i₃) ·ᵗ i₁ ≾ᵗ (i₂ ·ᵗ i₁) ⊔ᵗ (i₃ ·ᵗ i₁)
·ᵗ-distribʳ-⊔ᵗ (timed i) (timed j) (timed k) = ·ₒ-distribʳ-⊔ₒ i j k
·ᵗ-distribʳ-⊔ᵗ (timed _) (timed _) untimed   = tt
·ᵗ-distribʳ-⊔ᵗ untimed   (timed _) (timed _) = tt
·ᵗ-distribʳ-⊔ᵗ untimed   (timed _) untimed   = tt
·ᵗ-distribʳ-⊔ᵗ _         untimed   _         = tt

-- the grade of one-sided intervals with a formal greatest grade

-- every grade absorbs its own iteration, and is its own closure

·ᵗ-iter : (i : 𝕀⊤) → i ·ᵗ i ≾ᵗ i
·ᵗ-iter (timed i) = ·ₒ-iter i
·ᵗ-iter untimed   = tt

left-sided-intervals-with-⊤ : Grade ℕᴰ
left-sided-intervals-with-⊤ = posetᵍ record
  { Carrier           = 𝕀⊤
  ; _·_               = _·ᵗ_
  ; u                 = uᵗ
  ; ·-identityʳ       = ·ᵗ-identityʳ
  ; ·-identityˡ       = ·ᵗ-identityˡ
  ; ·-assoc           = ·ᵗ-assoc
  ; _≾_               = _≾ᵗ_
  ; ⊤                 = untimed
  ; ≾-⊤               = ≾ᵗ-⊤
  ; u-least?          = nothing
  ; ·-comm?           = just ·ᵗ-comm
  ; plus?             = λ i → just (plus-self (≾ᵗ-refl {i}) (·ᵗ-iter i))
  ; _⊔_               = _⊔ᵗ_
  ; ⊔-ubˡ             = ⊔ᵗ-ubˡ
  ; ⊔-ubʳ             = ⊔ᵗ-ubʳ
  ; ⊔-lub             = λ {i₁} {i₂} {i₃} → ⊔ᵗ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾    = ·ᵗ-distribˡ-⊔ᵗ
  ; ·-distribʳ-⊔-≾    = ·ᵗ-distribʳ-⊔ᵗ
  ; ·-monoʳ-≾         = λ {i} {i₁} {i₂} → ·ᵗ-monoʳ-≾ᵗ {i} {i₁} {i₂}
  ; ·-monoˡ-≾         = λ {i} {i₁} {i₂} → ·ᵗ-monoˡ-≾ᵗ {i} {i₁} {i₂}
  ; ≾-refl            = λ {i} → ≾ᵗ-refl {i}
  ; ≾-trans           = λ {i₁} {i₂} {i₃} → ≾ᵗ-trans {i₁} {i₂} {i₃}
  ; ≾-antisym         = λ {i₁} {i₂} → ≾ᵗ-antisym {i₁} {i₂}
  ; _≾?_              = _≾ᵗ?_
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ᵗ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ᵗ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ᵗ-irrelevant {i₁} {i₂}
  ; of-dur            = λ n → timed [ n ,+∞⟩
  ; of-dur-zero       = refl
  ; of-dur-plus       = refl
  }

------------------------------------------------------------------------
-- Candidate grades for a rigid: the bounds `0, …, s+1`, `s` the sum of
-- the constants' bounds. Each side of an ordering in one rigid `j` is
-- a minimum of pieces `c + a·j`, `c ≤ s`, two of which cross below `s`,
-- so an ordering failing at some `j` fails at one of them.

private
  bound : 𝕀 → ℕ
  bound [ n ,+∞⟩ = n

left-sided-witnesses : ℕ → List 𝕀 → List 𝕀
left-sided-witnesses _ cs = mapᴸ [_,+∞⟩ (upTo (2 + sum (mapᴸ bound cs)))

-- with `untimed`, which no finite rigid gives, among the constants

left-sided-witnesses-with-⊤ : ℕ → List 𝕀⊤ → List 𝕀⊤
left-sided-witnesses-with-⊤ d cs = mapᴸ timed_ (left-sided-witnesses d (timeds cs))
  where
    timeds : List 𝕀⊤ → List 𝕀
    timeds []              = []
    timeds (timed i ∷ cs') = i ∷ timeds cs'
    timeds (untimed ∷ cs') = timeds cs'
