----------------------------------------
-- The natural numbers as durations   --
----------------------------------------

module Syntax.Durations.Nat where

open import Data.Nat.Base using (ℕ; _+_; _≤_; _∸_)
open import Data.Nat.Properties
  using (+-identityʳ; +-assoc; +-comm; +-cancelˡ-≡; _≤?_; ≤-refl; ≤-trans;
         ≤-antisym; ≤-total; m≤m+n; m+[n∸m]≡n)
open import Data.Product using (_,_)

open import Syntax.Durations

open import Util.Equality

-- Discrete time: a duration is a number of time steps

ℕᴰ : Duration
ℕᴰ = record
  { Carrier      = ℕ
  ; _+ᴰ_         = _+_
  ; 0ᴰ           = 0
  ; +ᴰ-identityˡ = λ _ → refl
  ; +ᴰ-identityʳ = +-identityʳ
  ; +ᴰ-assoc     = +-assoc
  }

ℕᴰ-stepped : Stepped ℕᴰ
ℕᴰ-stepped = record
  { toℕ       = λ n → n
  ; fromℕ     = λ n → n
  ; toℕ-fromℕ = λ _ → refl
  ; fromℕ-toℕ = λ _ → refl
  ; toℕ-0     = refl
  ; toℕ-+     = λ _ _ → refl
  }

-- the natural numbers under their usual order form a time domain

ℕᵀ : TimeDomain ℕᴰ
ℕᵀ = record
  { +ᴰ-comm    = +-comm
  ; +ᴰ-cancelˡ = λ m {n} {o} → +-cancelˡ-≡ m n o
  ; _≤ᴰ_       = _≤_
  ; _≤ᴰ?_      = _≤?_
  ; ≤ᴰ-refl    = ≤-refl
  ; ≤ᴰ-trans   = ≤-trans
  ; ≤ᴰ-antisym = ≤-antisym
  ; ≤ᴰ-total   = ≤-total
  ; ≤ᴰ-+       = m≤m+n
  ; diff       = λ {m} {n} p → n ∸ m , m+[n∸m]≡n p
  }
