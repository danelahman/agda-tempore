------------------------------------------------------------------------
-- Finite timed regex grades over the non-negative rationals, as      --
-- lower bounds.                                                      --
--                                                                    --
-- Letters reach up without bound: `≥ q` and `> q` time spans of at   --
-- least and of more than `q` in which any operation may run, `e & S` --
-- the time span `e` admitting only the operations of `S`, and        --
-- `idle e` the time span `e` admitting none, an idle wait:           --
-- `idle ≥ q` of at least `q`, `idle > q` of more than `q`. Activity  --
-- before, between and after operations is allowed only by explicit   --
-- time spans such as `≥ 0`, so the empty word is not the greatest    --
-- grade. A delay is graded by the wait of at least its length, the   --
-- delay zero by the empty word.                                      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.Traces.TimedRegex.Finite.LowerBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Data.Vec.Base using (foldr′)

open import Grades.Base using (Grade)
open import Grades.Durations.Monus ℚ≥0ᵀ using (Carrier)
open import Grades.Durations.Intervals ℚ≥0ᵀ using (⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Grades.Examples.Traces.TimedRegex.Finite.Base Op n code name name-code code-name running public

------------------------------------------------------------------------
-- Letters

Lower : Set
Lower = Expr lower

≥_ >_ : Carrier → Lower
≥ d = str all (d ∣ᶜ ⁻)
> d = str all (d ∣ᶜ ⁺)

infix 9   ≥_ >_
infix 8.5 idle_
infix 8   _&_

_&_ : Lower → OpSet → Lower
str _ e & S = str S e
e       & _ = e

-- whether an expression is a time span admitting every operation

span? : Lower → Bool
span? (str S _) = foldr′ _∧_ true S
span? _         = false

-- an idle wait: a time span admitting every operation, restricted to
-- admit none

idle_ : (e : Lower) {_ : T (span? e)} → Lower
idle e = e & none

------------------------------------------------------------------------
-- The grade

lower-bound : Grade ℚ≥0ᴰ
lower-bound = lowerᵍ
