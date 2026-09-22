------------------------------------------------------------------------
-- Strictly positive durations.                                        --
--                                                                     --
-- Delays in a timed trace carry a strictly positive duration, so that  --
-- zero-valued delays cannot appear in a trace. A small dedicated type  --
-- of positive naturals with its addition is what enforces that.        --
--                                                                     --
-- Nothing here mentions operations, so this layer is independent of    --
-- the alphabet `Op` the rest of the trace toolkit is parameterised by. --
------------------------------------------------------------------------

module Syntax.Grades.Traces.Positive where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)

open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Nullary using (yes; no)

open import Util.Equality

------------------------------------------------------------------------
-- The type and its addition

data ℕ⁺ : Set where
  𝟏    : ℕ⁺
  suc⁺ : ℕ⁺ → ℕ⁺

infixl 6 _+⁺_

_+⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
𝟏      +⁺ n = suc⁺ n
suc⁺ m +⁺ n = suc⁺ (m +⁺ n)

+⁺-assoc : (m n o : ℕ⁺) → ((m +⁺ n) +⁺ o) ≡ (m +⁺ (n +⁺ o))
+⁺-assoc 𝟏        n o = refl
+⁺-assoc (suc⁺ m) n o = cong suc⁺ (+⁺-assoc m n o)

_≟⁺_ : DecidableEquality ℕ⁺
𝟏      ≟⁺ 𝟏      = yes refl
𝟏      ≟⁺ suc⁺ _ = no λ ()
suc⁺ _ ≟⁺ 𝟏      = no λ ()
suc⁺ m ≟⁺ suc⁺ n with m ≟⁺ n
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }

------------------------------------------------------------------------
-- Reading a positive duration off a natural number

-- the positive natural `1 + n`

infix 8 1+_

1+_ : ℕ → ℕ⁺
1+ zero    = 𝟏
1+ (suc n) = suc⁺ (1+ n)

1+-+⁺ : (m n : ℕ) → ((1+ m) +⁺ (1+ n)) ≡ 1+ (m + suc n)
1+-+⁺ zero    n = refl
1+-+⁺ (suc m) n = cong suc⁺ (1+-+⁺ m n)

------------------------------------------------------------------------
-- Cancellation
--
-- What the left cancellativity of the trace monoid rests on: prepending
-- a fixed delay is injective because adding a fixed duration is.

-- injectivity of `suc⁺`

suc⁺-inj : ∀ {m n} → suc⁺ m ≡ suc⁺ n → m ≡ n
suc⁺-inj refl = refl

-- left cancellation of positive-duration addition

+⁺-cancelˡ : (d : ℕ⁺) {e e' : ℕ⁺} → d +⁺ e ≡ d +⁺ e' → e ≡ e'
+⁺-cancelˡ 𝟏        eq = suc⁺-inj eq
+⁺-cancelˡ (suc⁺ d) eq = +⁺-cancelˡ d (suc⁺-inj eq)

-- a positive duration is never equal to a strictly larger one

d≢d+⁺e : (d e : ℕ⁺) → d +⁺ e ≡ d → ⊥
d≢d+⁺e 𝟏        e ()
d≢d+⁺e (suc⁺ d) e eq = d≢d+⁺e d e (suc⁺-inj eq)

------------------------------------------------------------------------
-- The strict total order
--
-- The usual order on the naturals, read off the unary representation.

infix 4 _<⁺_

data _<⁺_ : ℕ⁺ → ℕ⁺ → Set where
  𝟏<suc⁺    : {n : ℕ⁺} → 𝟏 <⁺ suc⁺ n
  suc⁺<suc⁺ : {m n : ℕ⁺} → m <⁺ n → suc⁺ m <⁺ suc⁺ n

<⁺-trans : Transitive _<⁺_
<⁺-trans 𝟏<suc⁺       (suc⁺<suc⁺ _) = 𝟏<suc⁺
<⁺-trans (suc⁺<suc⁺ p) (suc⁺<suc⁺ q) = suc⁺<suc⁺ (<⁺-trans p q)

<⁺-cmp : Trichotomous _≡_ _<⁺_
<⁺-cmp 𝟏        𝟏        = tri≈ (λ ()) refl (λ ())
<⁺-cmp 𝟏        (suc⁺ n) = tri< 𝟏<suc⁺ (λ ()) (λ ())
<⁺-cmp (suc⁺ m) 𝟏        = tri> (λ ()) (λ ()) 𝟏<suc⁺
<⁺-cmp (suc⁺ m) (suc⁺ n) with <⁺-cmp m n
... | tri< p ¬q ¬r =
        tri< (suc⁺<suc⁺ p)
             (λ { refl → ¬q refl })
             (λ { (suc⁺<suc⁺ r) → ¬r r })
... | tri≈ ¬p refl ¬r =
        tri≈ (λ { (suc⁺<suc⁺ p) → ¬p p })
             refl
             (λ { (suc⁺<suc⁺ r) → ¬r r })
... | tri> ¬p ¬q r =
        tri> (λ { (suc⁺<suc⁺ p) → ¬p p })
             (λ { refl → ¬q refl })
             (suc⁺<suc⁺ r)
