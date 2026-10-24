------------------------------------------------------------------------
-- Rigid timed regular grades in whole steps, as lower bounds.        --
--                                                                    --
-- A grade is written with one-sided letters whose lengths reach up   --
-- to no bound: `≥ d` a stretch of at least `d` in which any          --
-- operation may run, `> d` one longer than `d`, `≥ d & S` one in     --
-- which only those of `S` may, and `idle ≥ d` a strict wait of at    --
-- least `d`, in which none may. Activity before, between and after   --
-- is admitted only where a stretch says so -- `≥ 0` is the flank     --
-- admitting anything -- so the empty word is not the greatest grade. --
-- A delay of `d` steps is graded by `d` strict waits of at least a   --
-- step each, the hull of the delay on this side (`Exact.Hull`).      --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᴰ; ℕᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Regular.LeftSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℕᵀ Op) where

open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)

open import Syntax.Grades using (Grade)
open import Syntax.Durations.Intervals ℕᵀ using (⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades.Example.Traces.Rigid.Regular.Base Op n code name name-code code-name running public

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

-- a stretch admitting only the operations of a set

_&_ : Lower → OpSet → Lower
str _ c & S = str S c
e       & _ = e

-- a strict wait, the stretch admitting no operation

idle_ : Lower → Lower
idle e = e & none

------------------------------------------------------------------------
-- The grade

of-dur : ℕ → Closed
of-dur = steps wait≥1

left-sided : Grade ℕᴰ
left-sided =
  C.WithDurations.closed-grade of-dur refl (λ {m} {n} → steps-plus wait≥1 {m} {n})
