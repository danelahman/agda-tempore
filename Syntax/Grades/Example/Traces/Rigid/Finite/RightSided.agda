------------------------------------------------------------------------
-- Rigid timed finite-expression grades over the non-negative         --
-- rationals, as upper bounds.                                        --
--                                                                    --
-- Letters reach down to zero: `≤ q` and `< q` stretches of at most   --
-- and of less than `q` in which any operation may run, `≤∞` one of   --
-- any length, `e & S` the stretch `e` admitting only the operations  --
-- of `S`, and `idle e` the stretch `e` admitting none, a strict      --
-- wait: `idle ≤ q` of at most `q`, `idle < q` of less than `q`. A    --
-- delay is graded by the wait of at most its length, the hull of the --
-- delay on this side.                                                --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Finite.RightSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)

open import Syntax.Grades using (Grade)
open import Syntax.Durations.Monus ℚ≥0ᵀ using (Carrier)
open import Syntax.Durations.Intervals ℚ≥0ᵀ using (fin; ∞; ⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades.Example.Traces.Rigid.Finite.Base Op n code name name-code code-name running public

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

-- a stretch admitting only the operations of a set

_&_ : Upper → OpSet → Upper
str _ e & S = str S e
e       & _ = e

-- a strict wait, the stretch admitting no operation

idle_ : Upper → Upper
idle e = e & none

≤∞ : Upper
≤∞ = str all ∞

------------------------------------------------------------------------
-- The grade

right-sided : Grade ℚ≥0ᴰ
right-sided = upperᵍ
