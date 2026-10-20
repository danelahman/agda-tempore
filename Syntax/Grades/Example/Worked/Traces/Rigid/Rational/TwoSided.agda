------------------------------------------------------------------------
-- Worked rigid timed regular-expression intervals in dense time.     --
--                                                                    --
-- An interval `[ L , U ]` pairs a lower and an upper bound. Here a   --
-- cycle: heating, then a rest of at least one unit and at most three,--
-- repeated at least once. Delays are graded by both hulls, a wait of --
-- exactly their length.                                              --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Rational.TwoSided where

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Product using (_×_; _,_)

open import Util.Equality

open import Syntax.Grades.Example.Time.Dense.TwoSided using (_/_; #_)
open import Syntax.Grades.Example.Worked.Traces.Rigid.Finite.Operations
open import Syntax.Grades.Example.Traces.Rigid.Rational.TwoSided Op 3 code name name-code code-name running
open import Syntax.Grades.Example.Traces.Rigid.Rational.Base Op 3 code name name-code code-name running
  using (Proper′; ⌜_⌝; holds; waitᴸ; waitᵁ; lower; upper; _·_; ‵_; _·ᵉ_; _⁺ᵉ)
import Syntax.Grades.Example.Traces.Rigid.Rational.LeftSided Op 3 code name name-code code-name running as L
import Syntax.Grades.Example.Traces.Rigid.Rational.RightSided Op 3 code name name-code code-name running as U

-- componentwise comparison and sequencing

holds₂ : Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper → Bool
holds₂ (l , u) (l′ , u′) = holds l l′ ∧ holds u u′

infixl 7 _·₂_

_·₂_ : Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper → Proper′ lower × Proper′ upper
(l , u) ·₂ (l′ , u′) = (l ·ᵉ l′) , (u ·ᵉ u′)

-- heating, then a rest of between one and three units, at least once

cycle : Proper′ lower × Proper′ upper
cycle = [ ⌜ ‵ heat · L.!≥ (# 1) ⌝ ⁺ᵉ , ⌜ ‵ heat · U.!≤ (# 3) ⌝ ⁺ᵉ ]

heating : Proper′ lower × Proper′ upper
heating = ⌜ ‵ heat ⌝ , ⌜ ‵ heat ⌝

rest : _ → Proper′ lower × Proper′ upper
rest τ = waitᴸ τ , waitᵁ τ

-- two cycles with rests of one and a half and of two meet it

twice : holds₂ (heating ·₂ rest (3 / 2) ·₂ heating ·₂ rest (# 2)) cycle ≡ true
twice = refl

-- a rest of half a unit is too short, one of four too long

hurried : holds₂ (heating ·₂ rest (1 / 2)) cycle ≡ false
hurried = refl

idle : holds₂ (heating ·₂ rest (# 4)) cycle ≡ false
idle = refl
