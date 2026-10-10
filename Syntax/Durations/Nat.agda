----------------------------------------
-- The natural numbers as durations   --
----------------------------------------

module Syntax.Durations.Nat where

open import Data.Nat.Base using (ℕ; _+_)
open import Data.Nat.Properties using (+-identityʳ; +-assoc)

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
