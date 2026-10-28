----------------------------------------
-- The natural numbers as durations   --
----------------------------------------

module Grades.Durations.Nat where

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _∸_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-identityʳ; +-assoc; +-comm; +-cancelˡ-≡; _≤?_; ≤-refl; ≤-trans;
         ≤-antisym; ≤-total; ≤-irrelevant; m≤m+n; m+[n∸m]≡n)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)

open import Grades.Durations

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

-- the natural numbers under their usual order form a discrete time
-- domain, the step being the least positive duration

private
  step-least : (n : ℕ) → ¬ (n ≤ 0) → 1 ≤ n
  step-least zero    p = ⊥-elim (p z≤n)
  step-least (suc n) _ = s≤s z≤n

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
  ; ≤ᴰ-irrelevant = ≤-irrelevant
  ; ≤ᴰ-+       = m≤m+n
  ; diff       = λ {m} {n} p → n ∸ m , m+[n∸m]≡n p
  ; grain      = discrete 1 (λ ()) step-least
  }

ℕᵀ-discrete : Discrete ℕᵀ
ℕᵀ-discrete = 1 , (λ ()) , step-least
