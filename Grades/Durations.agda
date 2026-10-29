---------------------------------------
-- Durations: the monoid of delays   --
---------------------------------------

module Grades.Durations where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (suc-injective; m+n≡0⇒m≡0; m+n≡0⇒n≡0)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Nullary using (¬_)

open import Util.Equality

-- Monoids of durations: `delay τ` lets the duration `τ` pass, and two
-- consecutive delays are the delay by the sum

record Duration : Set₁ where
  infixl 6 _+ᴰ_

  field
    Carrier : Set₀
    _+ᴰ_    : Carrier → Carrier → Carrier
    0ᴰ      : Carrier

    +ᴰ-identityˡ : (τ : Carrier) → 0ᴰ +ᴰ τ ≡ τ
    +ᴰ-identityʳ : (τ : Carrier) → τ +ᴰ 0ᴰ ≡ τ
    +ᴰ-assoc     : (τ τ' τ'' : Carrier) → (τ +ᴰ τ') +ᴰ τ'' ≡ τ +ᴰ (τ' +ᴰ τ'')


-- Monoid morphisms of durations

record _→ᴰ_ (D₁ D₂ : Duration) : Set where
  private
    module D₁ = Duration D₁
    module D₂ = Duration D₂
  field
    map   : D₁.Carrier → D₂.Carrier
    map-0 : map D₁.0ᴰ ≡ D₂.0ᴰ
    map-+ : ∀ {τ τ'} → map (τ D₁.+ᴰ τ') ≡ map τ D₂.+ᴰ map τ'

open _→ᴰ_

idᴰ : ∀ {D} → D →ᴰ D
idᴰ = record { map = λ τ → τ ; map-0 = refl ; map-+ = refl }

_∘ᴰ_ : ∀ {D₁ D₂ D₃} → D₂ →ᴰ D₃ → D₁ →ᴰ D₂ → D₁ →ᴰ D₃
g ∘ᴰ f = record
  { map   = λ τ → map g (map f τ)
  ; map-0 = trans (cong (map g) (map-0 f)) (map-0 g)
  ; map-+ = trans (cong (map g) (map-+ f)) (map-+ g)
  }


-- Stepped durations: a monoid isomorphism with `ℕ`, a duration being a
-- number of unit steps

record Stepped (D : Duration) : Set where
  open Duration D
  field
    toℕ       : Carrier → ℕ
    fromℕ     : ℕ → Carrier
    toℕ-fromℕ : (n : ℕ) → toℕ (fromℕ n) ≡ n
    fromℕ-toℕ : (τ : Carrier) → fromℕ (toℕ τ) ≡ τ
    toℕ-0     : toℕ 0ᴰ ≡ 0
    toℕ-+     : (τ τ' : Carrier) → toℕ (τ +ᴰ τ') ≡ toℕ τ + toℕ τ'

  -- the inverse is a monoid morphism as well
  fromℕ-0 : fromℕ 0 ≡ 0ᴰ
  fromℕ-0 = trans (cong fromℕ (sym toℕ-0)) (fromℕ-toℕ 0ᴰ)

  fromℕ-+ : (m n : ℕ) → fromℕ (m + n) ≡ fromℕ m +ᴰ fromℕ n
  fromℕ-+ m n =
    trans (cong fromℕ (sym (cong₂ _+_ (toℕ-fromℕ m) (toℕ-fromℕ n))))
          (trans (cong fromℕ (sym (toℕ-+ (fromℕ m) (fromℕ n))))
                 (fromℕ-toℕ (fromℕ m +ᴰ fromℕ n)))

  -- the unit step
  1ᴰ : Carrier
  1ᴰ = fromℕ 1

  toℕ-injective : ∀ {τ τ'} → toℕ τ ≡ toℕ τ' → τ ≡ τ'
  toℕ-injective {τ} {τ'} e =
    trans (sym (fromℕ-toℕ τ)) (trans (cong fromℕ e) (fromℕ-toℕ τ'))

  toℕ-1+ : (τ : Carrier) → toℕ (1ᴰ +ᴰ τ) ≡ suc (toℕ τ)
  toℕ-1+ τ = trans (toℕ-+ 1ᴰ τ) (cong (_+ toℕ τ) (toℕ-fromℕ 1))

  -- a duration is no time, or a step followed by a duration
  zero-or-step : (τ : Carrier) → (τ ≡ 0ᴰ) ⊎ Σ Carrier (λ τ' → τ ≡ 1ᴰ +ᴰ τ')
  zero-or-step τ = go (toℕ τ) refl
    where
      go : (m : ℕ) → toℕ τ ≡ m → (τ ≡ 0ᴰ) ⊎ Σ Carrier (λ τ' → τ ≡ 1ᴰ +ᴰ τ')
      go zero    e = inj₁ (toℕ-injective (trans e (sym toℕ-0)))
      go (suc m) e = inj₂ (fromℕ m , toℕ-injective
                             (trans e (sym (trans (toℕ-1+ (fromℕ m))
                                                  (cong suc (toℕ-fromℕ m))))))

  1+≢0ᴰ : ∀ {τ} → 1ᴰ +ᴰ τ ≡ 0ᴰ → ⊥
  1+≢0ᴰ {τ} e with trans (sym (toℕ-1+ τ)) (trans (cong toℕ e) toℕ-0)
  ... | ()

  1+-cancel : ∀ {τ τ'} → 1ᴰ +ᴰ τ ≡ 1ᴰ +ᴰ τ' → τ ≡ τ'
  1+-cancel {τ} {τ'} e =
    toℕ-injective (suc-injective (trans (sym (toℕ-1+ τ)) (trans (cong toℕ e) (toℕ-1+ τ'))))

  -- no time is a sum only of no time
  zero-sumˡ : ∀ {τ τ'} → τ +ᴰ τ' ≡ 0ᴰ → τ ≡ 0ᴰ
  zero-sumˡ {τ} {τ'} e =
    toℕ-injective (trans (m+n≡0⇒m≡0 (toℕ τ) (trans (sym (toℕ-+ τ τ')) (trans (cong toℕ e) toℕ-0)))
                         (sym toℕ-0))

  zero-sumʳ : ∀ {τ τ'} → τ +ᴰ τ' ≡ 0ᴰ → τ' ≡ 0ᴰ
  zero-sumʳ {τ} {τ'} e =
    toℕ-injective (trans (m+n≡0⇒n≡0 (toℕ τ) (trans (sym (toℕ-+ τ τ')) (trans (cong toℕ e) toℕ-0)))
                         (sym toℕ-0))


-- The grain of a totally ordered set with a least element `0`: dense,
-- a third element lying between any two distinct ones, or discrete,
-- with a least element above `0`

data Grain {C : Set₀} (_≤_ : C → C → Set₀) (0ᴰ : C) : Set₀ where
  dense    : ({τ τ' : C} → ¬ (τ' ≤ τ) → Σ C (λ τ'' → ¬ (τ'' ≤ τ) × ¬ (τ' ≤ τ'')))
           → Grain _≤_ 0ᴰ
  discrete : (ε : C) → ¬ (ε ≤ 0ᴰ) → ((τ : C) → ¬ (τ ≤ 0ᴰ) → ε ≤ τ)
           → Grain _≤_ 0ᴰ


-- Time domains: durations that are compared and subtracted. A time
-- domain is a commutative, cancellative monoid of durations with a
-- decidable total order in which `τ ≤ τ'` exactly when `τ'` is `τ`
-- followed by some further duration -- the positive cone of a totally
-- ordered abelian group -- and which is dense or discrete. The
-- difference, the truncated subtraction and the extremal operations
-- are derived from these fields in `Durations.Monus`.

record TimeDomain (D : Duration) : Set₁ where
  open Duration D
  infix 4 _≤ᴰ_ _≤ᴰ?_

  field
    +ᴰ-comm    : (τ τ' : Carrier) → τ +ᴰ τ' ≡ τ' +ᴰ τ
    +ᴰ-cancelˡ : (τ : Carrier) {τ' τ'' : Carrier} → τ +ᴰ τ' ≡ τ +ᴰ τ'' → τ' ≡ τ''

    _≤ᴰ_       : Carrier → Carrier → Set₀
    _≤ᴰ?_      : Decidable _≤ᴰ_
    ≤ᴰ-refl    : {τ : Carrier} → τ ≤ᴰ τ
    ≤ᴰ-trans   : {τ τ' τ'' : Carrier} → τ ≤ᴰ τ' → τ' ≤ᴰ τ'' → τ ≤ᴰ τ''
    ≤ᴰ-antisym : {τ τ' : Carrier} → τ ≤ᴰ τ' → τ' ≤ᴰ τ → τ ≡ τ'
    ≤ᴰ-total   : (τ τ' : Carrier) → τ ≤ᴰ τ' ⊎ τ' ≤ᴰ τ
    -- a comparison is a proposition
    ≤ᴰ-irrelevant : {τ τ' : Carrier} (p q : τ ≤ᴰ τ') → p ≡ q

    -- the order is the one the monoid induces: a summand is below the
    -- sum, and what lies above `τ` is `τ` followed by a difference
    ≤ᴰ-+       : (τ τ' : Carrier) → τ ≤ᴰ τ +ᴰ τ'
    diff       : {τ τ' : Carrier} → τ ≤ᴰ τ' → Σ Carrier (λ κ → τ +ᴰ κ ≡ τ')

    grain      : Grain _≤ᴰ_ 0ᴰ


-- Dense time domains: between two distinct durations lies a third

Dense : {D : Duration} → TimeDomain D → Set₀
Dense {D} T = {τ τ' : Carrier} → ¬ (τ' ≤ᴰ τ)
            → Σ Carrier (λ τ'' → ¬ (τ'' ≤ᴰ τ) × ¬ (τ' ≤ᴰ τ''))
  where
    open Duration D
    open TimeDomain T


-- Discrete time domains: a least positive duration, a step

Discrete : {D : Duration} → TimeDomain D → Set₀
Discrete {D} T = Σ Carrier (λ ε → ¬ (ε ≤ᴰ 0ᴰ) × ((τ : Carrier) → ¬ (τ ≤ᴰ 0ᴰ) → ε ≤ᴰ τ))
  where
    open Duration D
    open TimeDomain T

-- no time domain is both

dense-discrete : {D : Duration} {T : TimeDomain D} → Dense T → Discrete T → ⊥
dense-discrete {D} {T} d (ε , ε-pos , ε-least) with d ε-pos
... | τ , τ-pos , ε≰τ = ε≰τ (ε-least τ τ-pos)
