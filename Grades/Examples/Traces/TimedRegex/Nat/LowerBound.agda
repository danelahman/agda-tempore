------------------------------------------------------------------------
-- Timed regex grades in whole steps, as lower bounds.                --
--                                                                    --
-- A grade is written with one-sided letters whose lengths reach up   --
-- to no bound: `≥ d` a time span of at least `d` in which any        --
-- operation may run, `> d` one longer than `d`, `≥ d & S` one in     --
-- which only those of `S` may, and `idle ≥ d` an idle wait of at     --
-- least `d`, in which none may. Activity before, between and after   --
-- is admitted only where a time span says so (`≥ 0` is the flank     --
-- admitting anything), so the empty word is not the greatest grade.  --
-- A delay of `d` steps is graded by `d` idle waits of at least a     --
-- step each, the hull of the delay on this side (`Exact.Hull`).      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᴰ; ℕᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.Traces.TimedRegex.Nat.LowerBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Data.Vec.Base using (foldr′)

open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Durations.Intervals ℕᵀ using (⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Grades.Examples.Traces.TimedRegex.Nat.Base Op n code name name-code code-name running public

------------------------------------------------------------------------
-- Letters

Lower : Set
Lower = Expr lower

≥_ >_ : ℕ → Lower
≥ d = str all (d ∣ᶜ ⁻)
> d = str all (d ∣ᶜ ⁺)

infix 9   ≥_ >_
infix 8.5 idle_
infix 8   _&_

-- a time span admitting only the operations of a set

_&_ : Lower → OpSet → Lower
str _ c & S = str S c
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

ι : ℕ → Closed
ι = steps wait≥1

lower-bound : Grade ℕᴰ
lower-bound =
  C.WithDurations.closed-grade ι refl (λ {m} {n} → steps-plus wait≥1 {m} {n})

-- its hints by copatterns, so that `lower-bound` is not compared as a
-- record value

private
  module H = GradeHints
    (C.WithDurations.closed-gradeʰ ι refl (λ {m} {n} → steps-plus wait≥1 {m} {n}))

lower-boundʰ : GradeHints lower-bound
GradeHints.𝟏-least? lower-boundʰ = H.𝟏-least?
GradeHints.·-comm?  lower-boundʰ = H.·-comm?
GradeHints.plus?    lower-boundʰ = H.plus?
