------------------------------------------------------------------------
-- Timed regex grades in whole steps, as upper bounds.                --
--                                                                    --
-- A grade is written with one-sided letters whose lengths reach down --
-- to zero: `≤ d` a time span of at most `d` in which any operation   --
-- may run, `≤ d & S` one in which only those of `S` may, `≤∞` one of --
-- any length, and `idle ≤ d` an idle wait of at most `d`, in which   --
-- none may. A delay of `d` steps is graded by `d` idle waits of at   --
-- most a step each, the hull of the delay on this side               --
-- (`Exact.Hull`).                                                    --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᴰ; ℕᵀ)
import Grades.Traces.RunningTimes as RunningTimes

module Grades.Examples.Traces.TimedRegex.Nat.UpperBound
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Bool.Base using (Bool; true; false; _∧_; T)
open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)
open import Data.Vec.Base using (foldr′)

open import Grades.Base using (Grade)
open import Grades.Hints using (GradeHints)
open import Grades.Durations.Intervals ℕᵀ using (fin; ∞; ⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Grades.Examples.Traces.TimedRegex.Nat.Base Op n code name name-code code-name running public

------------------------------------------------------------------------
-- Letters

Upper : Set
Upper = Expr upper

≤_ <_ : ℕ → Upper
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

ι : ℕ → Closed
ι = steps wait≤1

upper-bound : Grade ℕᴰ
upper-bound =
  C.WithDurations.closed-grade ι refl (λ {m} {n} → steps-plus wait≤1 {m} {n})

-- its hints by copatterns, so that `upper-bound` is not compared as a
-- record value

private
  module H = GradeHints
    (C.WithDurations.closed-gradeʰ ι refl (λ {m} {n} → steps-plus wait≤1 {m} {n}))

upper-boundʰ : GradeHints upper-bound
GradeHints.𝟏-least? upper-boundʰ = H.𝟏-least?
GradeHints.·-comm?  upper-boundʰ = H.·-comm?
GradeHints.plus?    upper-boundʰ = H.plus?
