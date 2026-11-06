------------------------------------------------------------------------
-- Rational timed regex grades, as upper bounds.                      --
--                                                                    --
-- Letters reach down to zero: `≤ q` and `< q` time spans of at most  --
-- and of less than `q` in which any operation may run, `≤∞` one of   --
-- any length, `e & S` the time span `e` admitting only the           --
-- operations of `S`, and `idle e` the time span `e` admitting none,  --
-- an idle wait: `idle ≤ q` of at most `q`, `idle < q` of less than   --
-- `q`. A delay is graded by the wait of at most its length, the hull --
-- of the delay on this side.                                         --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.Traces.TimedRegex.Rational.UpperBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Data.Vec.Base using (foldr′)

open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Durations.Monus ℚ≥0ᵀ using (Carrier)
open import Grades.Durations.Intervals ℚ≥0ᵀ using (fin; ∞; ⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Grades.Examples.Traces.TimedRegex.Rational.Base Op n code name name-code code-name running public

------------------------------------------------------------------------
-- Letters

Upper : Set
Upper = Expr upper

≤_ <_ : Carrier → Upper
≤ d = str all (fin (d ∣ᶜ ⁺))
< d = str all (fin (d ∣ᶜ ⁻))

infix 9   ≤_ <_
infix 8.5 idle_
infix 8   _&_

-- a time span admitting only the operations of a set

_&_ : Upper → OpSet → Upper
str _ e & S = str S e
e       & _ = e

-- whether an expression is a time span admitting every operation

span? : Upper → Bool
span? (str S _) = foldr′ _∧_ true S
span? _         = false

-- an idle wait: a time span admitting every operation, restricted to
-- admit none

idle_ : (e : Upper) {_ : T (span? e)} → Upper
idle e = e & none

≤∞ : Upper
≤∞ = str all ∞

------------------------------------------------------------------------
-- The grade

upper-bound : Grade ℚ≥0ᴰ
upper-bound = upperᵍ

upper-boundʰ : GradeHints upper-bound
upper-boundʰ = upperʰ
