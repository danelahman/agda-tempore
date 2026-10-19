------------------------------------------------------------------------
-- Rigid timed regular grades in whole steps, as upper bounds.        --
--                                                                    --
-- A grade is written with one-sided letters whose lengths reach down --
-- to zero: `!≤ d` a strict wait of at most `d`, `≤ d` a stretch of   --
-- at most `d` in which any operation may run, `≤ d & S` one in which --
-- only those of `S` may, `≤∞` one of any length. A delay of `d`      --
-- steps is graded by `d` strict waits of at most a step each, the    --
-- hull of the delay on this side (`Exact.Hull`).                     --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᴰ; ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Regular.RightSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)

open import Syntax.Grades using (Grade)
open import Syntax.Durations.Intervals ℕᵀ using (fin; ∞; ⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades.Example.Traces.Rigid.Regular.Base Op n code name name-code code-name running public

------------------------------------------------------------------------
-- Letters

Upper : Set
Upper = Expr upper

!≤_ !<_ ≤_ <_ : ℕ → Upper
!≤ d = str none (fin (d ∣ᶜ ⁺))
!< d = str none (fin (d ∣ᶜ ⁻))
≤ d  = str all (fin (d ∣ᶜ ⁺))
< d  = str all (fin (d ∣ᶜ ⁻))

infix 9 !≤_ !<_ ≤_ <_
infix 8 _&_

-- a stretch admitting only the operations of a set

_&_ : Upper → OpSet → Upper
str _ e & S = str S e
e       & _ = e

≤∞ : Upper
≤∞ = str all ∞

------------------------------------------------------------------------
-- The grade

of-dur : ℕ → Closed
of-dur = steps wait≤1

right-sided : Grade ℕᴰ
right-sided =
  C.WithDurations.closed-grade of-dur refl (λ {m} {n} → steps-plus wait≤1 {m} {n})
