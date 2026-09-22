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

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties using (≤-antisym; n∸n≡0; suc-injective)

open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; yes; no)

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
-- Positive durations and the natural numbers
--
-- The two directions of the correspondence: `1+ n` is the positive
-- duration `1 + n`, and `∣ d ∣⁺` is the length of `d` as a natural
-- number. Taking the length is a monoid homomorphism
-- `(ℕ⁺, +⁺) → (ℕ, +)`, and it is injective, so a delay is determined
-- by how long it lasts.

-- the positive natural `1 + n`

infix 8 1+_

1+_ : ℕ → ℕ⁺
1+ zero    = 𝟏
1+ (suc n) = suc⁺ (1+ n)

1+-+⁺ : (m n : ℕ) → ((1+ m) +⁺ (1+ n)) ≡ 1+ (m + suc n)
1+-+⁺ zero    n = refl
1+-+⁺ (suc m) n = cong suc⁺ (1+-+⁺ m n)

-- the length of a positive duration as a natural number

∣_∣⁺ : ℕ⁺ → ℕ
∣ 𝟏      ∣⁺ = suc zero
∣ suc⁺ n ∣⁺ = suc ∣ n ∣⁺

∣∣⁺-+⁺ : (d e : ℕ⁺) → ∣ d +⁺ e ∣⁺ ≡ ∣ d ∣⁺ + ∣ e ∣⁺
∣∣⁺-+⁺ 𝟏        e = refl
∣∣⁺-+⁺ (suc⁺ d) e = cong suc (∣∣⁺-+⁺ d e)

∣1+∣⁺ : (n : ℕ) → ∣ 1+ n ∣⁺ ≡ suc n
∣1+∣⁺ zero    = refl
∣1+∣⁺ (suc n) = cong suc (∣1+∣⁺ n)

-- a length is never zero

∣∣⁺-nz : (d : ℕ⁺) → ¬ (∣ d ∣⁺ ≡ 0)
∣∣⁺-nz 𝟏        ()
∣∣⁺-nz (suc⁺ _) ()

-- and it determines the duration

∣∣⁺-inj : {d e : ℕ⁺} → ∣ d ∣⁺ ≡ ∣ e ∣⁺ → d ≡ e
∣∣⁺-inj {𝟏}      {𝟏}      _  = refl
∣∣⁺-inj {𝟏}      {suc⁺ e} eq = ⊥-elim (∣∣⁺-nz e (sym (suc-injective eq)))
∣∣⁺-inj {suc⁺ d} {𝟏}      eq = ⊥-elim (∣∣⁺-nz d (suc-injective eq))
∣∣⁺-inj {suc⁺ d} {suc⁺ e} eq = cong suc⁺ (∣∣⁺-inj (suc-injective eq))

-- so two delays that bound each other are the same delay, and then
-- taking one from the other leaves nothing

same-delay : {d e : ℕ⁺} → ∣ d ∣⁺ ≤ ∣ e ∣⁺ → ∣ e ∣⁺ ≤ ∣ d ∣⁺ → d ≡ e
same-delay le₁ le₂ = ∣∣⁺-inj (≤-antisym le₁ le₂)

∣∣⁺-∸≡0 : {d e : ℕ⁺}
        → ∣ d ∣⁺ ≤ ∣ e ∣⁺ → ∣ e ∣⁺ ≤ ∣ d ∣⁺ → ∣ e ∣⁺ ∸ ∣ d ∣⁺ ≡ 0
∣∣⁺-∸≡0 {d} {e} le₁ le₂ =
  trans (cong (∣ e ∣⁺ ∸_) (≤-antisym le₁ le₂)) (n∸n≡0 ∣ e ∣⁺)

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
