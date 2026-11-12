------------------------------------------------------------------------
-- Lower bounds on rational time as grades.                           --
--                                                                    --
-- A grade `[ q ,+∞⟩` is a lower bound, "at least `q` time units",    --
-- with `q` a non-negative rational. Multiplication adds the bounds,  --
-- the order is the reverse of `≤` on them, and a smaller bound is    --
-- the weaker grade. A delay by `q` has grade `[ q ,+∞⟩`, so a delay  --
-- of half a unit has grade `[ 1 / 2 ,+∞⟩`.                           --
--                                                                    --
-- The lower bounds in whole steps of `Time.LowerBound` map here, by  --
-- a grade morphism along the inclusion of durations, a bound of `n`  --
-- time steps being read as `n` units of rational time.               --
------------------------------------------------------------------------

module Grades.Examples.Time.Rational.LowerBound where

open import Data.List.Base using (List; []; _∷_) renaming (map to mapᴸ)
open import Data.Nat.Base using (ℕ)
open import Data.Product
open import Data.Unit using (tt)

open import Level using () renaming (zero to lzero)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable.Core
open import Relation.Nullary.Negation.Core using (¬_)

open import Data.Maybe.Base using (just; nothing)

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℕ→ℚ≥0ᴰ)
open import Grades.Base
open import Grades.Hints using (GradeHints; comm-≡)

open import Util.Equality

-- the bound is a non-negative rational

open import Util.NonNegativeRational public

import Grades.Examples.Time.LowerBound as Discrete

-- type of time lower bounds

data 𝕀 : Set where
  [_,+∞⟩ : ℚ≥0 → 𝕀

-- equality helpers

eq𝕀 : ∀ {p q} → p ≡ q → [ p ,+∞⟩ ≡ [ q ,+∞⟩
eq𝕀 = cong [_,+∞⟩

𝕀-inj : ∀ {p q} → [ p ,+∞⟩ ≡ [ q ,+∞⟩ → p ≡ q
𝕀-inj refl = refl

-- interval addition

_·ₒ_ : 𝕀 → 𝕀 → 𝕀
[ p ,+∞⟩ ·ₒ [ q ,+∞⟩ = [ p + q ,+∞⟩

infixl 7 _·ₒ_

-- interval unit

𝟏ₒ : 𝕀
𝟏ₒ = [ 0ᵈ ,+∞⟩

-- interval order

_≾ₒ_ : Rel 𝕀 lzero
[ p ,+∞⟩ ≾ₒ [ q ,+∞⟩ = q ≤ p

infix 6 _≾ₒ_

-- identity laws

·ₒ-identityʳ : (i : 𝕀) → i ·ₒ 𝟏ₒ ≡ i
·ₒ-identityʳ [ p ,+∞⟩ = eq𝕀 (+-identityʳ p)

·ₒ-identityˡ : (i : 𝕀) → 𝟏ₒ ·ₒ i ≡ i
·ₒ-identityˡ [ p ,+∞⟩ = eq𝕀 (+-identityˡ p)

-- associativity

·ₒ-assoc : (i₁ i₂ i₃ : 𝕀) → (i₁ ·ₒ i₂) ·ₒ i₃ ≡ i₁ ·ₒ (i₂ ·ₒ i₃)
·ₒ-assoc [ p ,+∞⟩ [ q ,+∞⟩ [ r ,+∞⟩ = eq𝕀 (+-assoc p q r)

-- commutativity

·ₒ-comm : (i₁ i₂ : 𝕀) → i₁ ·ₒ i₂ ≡ i₂ ·ₒ i₁
·ₒ-comm [ p ,+∞⟩ [ q ,+∞⟩ = eq𝕀 (+-comm p q)

-- monotonicity

·ₒ-monoʳ-≾ₒ : ∀ {i} → (i ·ₒ_) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoʳ-≾ₒ {[ p ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} = +-monoʳ-≤ p

·ₒ-monoˡ-≾ₒ : ∀ {i} → (_·ₒ i) Preserves _≾ₒ_ ⟶ _≾ₒ_
·ₒ-monoˡ-≾ₒ {[ p ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} = +-monoˡ-≤ p

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

≾ₒ-⊤ : (i : 𝕀) → i ≾ₒ 𝟏ₒ
≾ₒ-⊤ [ p ,+∞⟩ = 0≤ p

-- decidability

_≾ₒ?_ : Decidable _≾ₒ_
[ p ,+∞⟩ ≾ₒ? [ q ,+∞⟩ = q ≤? p

-- the unit is not least: `[ 1 / 2 ,+∞⟩` lies strictly below it

𝟏ₒ-not-least : ¬ Minimum _≾ₒ_ 𝟏ₒ
𝟏ₒ-not-least least =
  toWitnessFalse {a? = [ 0ᵈ ,+∞⟩ ≾ₒ? [ 1 / 2 ,+∞⟩} tt (least [ 1 / 2 ,+∞⟩)

-- unit-product properties

≡ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≡ 𝟏ₒ → i₁ ≡ 𝟏ₒ
≡ₒ-zero-productˡ {[ p ,+∞⟩} {[ q ,+∞⟩} eq =
  eq𝕀 (≤0⇒≡0 (+-≤0ˡ {p} {q} (≤-reflexive (𝕀-inj eq))))

≡ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≡ 𝟏ₒ → i₂ ≡ 𝟏ₒ
≡ₒ-zero-productʳ {[ p ,+∞⟩} {[ q ,+∞⟩} eq =
  eq𝕀 (≤0⇒≡0 (+-≤0ʳ {p} {q} (≤-reflexive (𝕀-inj eq))))

≾ₒ-zero-productˡ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≾ₒ 𝟏ₒ → i₁ ≾ₒ 𝟏ₒ
≾ₒ-zero-productˡ {i₁} _ = ≾ₒ-⊤ i₁

≾ₒ-zero-productʳ : ∀ {i₁ i₂ : 𝕀} → i₁ ·ₒ i₂ ≾ₒ 𝟏ₒ → i₂ ≾ₒ 𝟏ₒ
≾ₒ-zero-productʳ {_} {i₂} _ = ≾ₒ-⊤ i₂

-- binary joins: a weaker grade has the smaller bound, so the join
-- takes the minimum of the two bounds

_⊔ₒ_ : 𝕀 → 𝕀 → 𝕀
[ p ,+∞⟩ ⊔ₒ [ q ,+∞⟩ = [ p ⊓ q ,+∞⟩

infixl 7 _⊔ₒ_

⊔ₒ-ubˡ : (i₁ i₂ : 𝕀) → i₁ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubˡ [ p ,+∞⟩ [ q ,+∞⟩ = ⊓-lbˡ p q

⊔ₒ-ubʳ : (i₁ i₂ : 𝕀) → i₂ ≾ₒ i₁ ⊔ₒ i₂
⊔ₒ-ubʳ [ p ,+∞⟩ [ q ,+∞⟩ = ⊓-lbʳ p q

⊔ₒ-lub : {i₁ i₂ i₃ : 𝕀} → i₁ ≾ₒ i₃ → i₂ ≾ₒ i₃ → i₁ ⊔ₒ i₂ ≾ₒ i₃
⊔ₒ-lub {[ _ ,+∞⟩} {[ _ ,+∞⟩} {[ _ ,+∞⟩} p q = ⊓-glb p q

-- addition distributes over the join, so the two sides are equal

·ₒ-distribˡ-⊔ₒ : (i₁ i₂ i₃ : 𝕀) → i₁ ·ₒ (i₂ ⊔ₒ i₃) ≾ₒ (i₁ ·ₒ i₂) ⊔ₒ (i₁ ·ₒ i₃)
·ₒ-distribˡ-⊔ₒ [ p ,+∞⟩ [ q ,+∞⟩ [ r ,+∞⟩ =
  ≤-reflexive (sym (+-distribˡ-⊓ p q r))

·ₒ-distribʳ-⊔ₒ : (i₁ i₂ i₃ : 𝕀) → (i₂ ⊔ₒ i₃) ·ₒ i₁ ≾ₒ (i₂ ·ₒ i₁) ⊔ₒ (i₃ ·ₒ i₁)
·ₒ-distribʳ-⊔ₒ [ p ,+∞⟩ [ q ,+∞⟩ [ r ,+∞⟩ =
  ≤-reflexive (sym (+-distribʳ-⊓ p q r))

-- the grade algebra of lower bounds on rational time

-- every grade absorbs its own iteration, and is its own closure

·ₒ-iter : (i : 𝕀) → i ·ₒ i ≾ₒ i
·ₒ-iter [ p ,+∞⟩ = p≤p+q p p

rational-lower-bound : Grade ℚ≥0ᴰ
rational-lower-bound = posetᵍ record
  { Carrier           = 𝕀
  ; _·_               = _·ₒ_
  ; 𝟏                 = 𝟏ₒ
  ; ·-identityʳ       = ·ₒ-identityʳ
  ; ·-identityˡ       = ·ₒ-identityˡ
  ; ·-assoc           = ·ₒ-assoc
  ; _≾_               = _≾ₒ_
  ; ⊤                 = 𝟏ₒ
  ; ≾-⊤               = ≾ₒ-⊤
  ; _⊔_               = _⊔ₒ_
  ; ⊔-ubˡ             = ⊔ₒ-ubˡ
  ; ⊔-ubʳ             = ⊔ₒ-ubʳ
  ; ⊔-lub             = λ {i₁} {i₂} {i₃} → ⊔ₒ-lub {i₁} {i₂} {i₃}
  ; ·-distribˡ-⊔-≾    = ·ₒ-distribˡ-⊔ₒ
  ; ·-distribʳ-⊔-≾    = ·ₒ-distribʳ-⊔ₒ
  ; ·-monoʳ-≾         = λ {i} {i₁} {i₂} → ·ₒ-monoʳ-≾ₒ {i} {i₁} {i₂}
  ; ·-monoˡ-≾         = λ {i} {i₁} {i₂} → ·ₒ-monoˡ-≾ₒ {i} {i₁} {i₂}
  ; ≾-refl            = λ {i} → ≾ₒ-refl {i}
  ; ≾-trans           = λ {i₁} {i₂} {i₃} → ≾ₒ-trans {i₁} {i₂} {i₃}
  ; ≾-antisym         = λ {i} {j} → ≾ₒ-antisym {i} {j}
  ; _≾?_              = _≾ₒ?_
  ; ≾-zero-productˡ   = λ {i₁} {i₂} → ≾ₒ-zero-productˡ {i₁} {i₂}
  ; ≾-zero-productʳ   = λ {i₁} {i₂} → ≾ₒ-zero-productʳ {i₁} {i₂}
  ; ≾-irrelevant      = λ {i₁} {i₂} → ≾ₒ-irrelevant {i₁} {i₂}
  ; ι                 = λ q → [ q ,+∞⟩
  ; ι-zero            = refl
  ; ι-plus            = refl
  }

-- its hints

rational-lower-boundʰ : GradeHints rational-lower-bound
rational-lower-boundʰ = record
  { 𝟏-least? = nothing
  ; ·-comm?  = just (comm-≡ rational-lower-bound ·ₒ-comm)
  ; plus?    = λ i → just (plus-self (≾ₒ-refl {i}) (·ₒ-iter i))
  }

------------------------------------------------------------------------
-- The lower bounds in whole steps, by a grade morphism

lower-bound→rational : GradeMorphism ℕ→ℚ≥0ᴰ Discrete.lower-bound
                                       rational-lower-bound
lower-bound→rational = strictᵍ record
  { map          = embed
  ; map-monotone = λ {i} {j} → mono {i} {j}
  ; map-𝟏        = refl
  ; map-·        = λ {i} {j} → hom {i} {j}
  ; map-⊤        = refl
  ; map-⊔        = λ {i} {j} → join {i} {j}
  ; map-ι        = refl
  }
  where
    embed : Discrete.𝕀 → 𝕀
    embed Discrete.[ n ,+∞⟩ = [ # n ,+∞⟩

    mono : ∀ {i j} → i Discrete.≾ₒ j → embed i ≾ₒ embed j
    mono {Discrete.[ _ ,+∞⟩} {Discrete.[ _ ,+∞⟩} = #-mono-≤

    hom : ∀ {i j} → embed (i Discrete.·ₒ j) ≡ embed i ·ₒ embed j
    hom {Discrete.[ m ,+∞⟩} {Discrete.[ n ,+∞⟩} = eq𝕀 (#-+ m n)

    join : ∀ {i j} → embed (i Discrete.⊔ₒ j) ≡ embed i ⊔ₒ embed j
    join {Discrete.[ m ,+∞⟩} {Discrete.[ n ,+∞⟩} = eq𝕀 (#-⊓ m n)

------------------------------------------------------------------------
-- Candidate grades for a rigid: the bounds of the grid of the
-- constants (`grid`)

rational-lower-bound-witnesses : ℕ → List 𝕀 → List 𝕀
rational-lower-bound-witnesses d cs = mapᴸ [_,+∞⟩ (grid d (mapᴸ bound cs))
  where
    bound : 𝕀 → ℚ≥0
    bound [ q ,+∞⟩ = q
