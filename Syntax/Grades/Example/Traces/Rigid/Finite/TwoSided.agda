------------------------------------------------------------------------
-- Rigid timed finite-expression grades over the non-negative         --
-- rationals, as intervals.                                           --
--                                                                    --
-- A grade `[ L , U ]` pairs a lower bound `L` with an upper bound    --
-- `U`, compared componentwise. A delay is graded by the waits of at  --
-- least and at most its length: together, a wait of exactly it.      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Finite.TwoSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Product using (_×_; _,_)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Product using (_×ᵍ_)

open import Syntax.Grades.Example.Traces.Rigid.Finite.Base Op n code name name-code code-name running

two-sided : Grade ℚ≥0ᴰ
two-sided = lowerᵍ ×ᵍ upperᵍ

[_,_] : Proper′ lower → Proper′ upper → Proper′ lower × Proper′ upper
[ L , U ] = L , U
