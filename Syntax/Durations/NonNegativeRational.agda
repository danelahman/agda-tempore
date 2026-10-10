----------------------------------------------------
-- The non-negative rationals as durations        --
----------------------------------------------------

module Syntax.Durations.NonNegativeRational where

open import Syntax.Durations
open import Syntax.Durations.Nat using (ℕᴰ)

open import Syntax.Grades.Example.Time.Dense.NonNegativeRational
  using (ℚ≥0; 0ᵈ; _+_; #_; #-+; +-identityˡ; +-identityʳ; +-assoc)

open import Util.Equality

-- Dense time: a duration is a non-negative rational number of time units

ℚ≥0ᴰ : Duration
ℚ≥0ᴰ = record
  { Carrier      = ℚ≥0
  ; _+ᴰ_         = _+_
  ; 0ᴰ           = 0ᵈ
  ; +ᴰ-identityˡ = +-identityˡ
  ; +ᴰ-identityʳ = +-identityʳ
  ; +ᴰ-assoc     = +-assoc
  }

-- the inclusion of discrete time, `n` steps being `n` units

ℕ→ℚ≥0ᴰ : ℕᴰ →ᴰ ℚ≥0ᴰ
ℕ→ℚ≥0ᴰ = record
  { map   = #_
  ; map-0 = refl
  ; map-+ = λ {m} {n} → #-+ m n
  }
