------------------------------------------------------------------------
-- Rigid timed regular-expression grades over the non-negative       --
-- rationals, as lower bounds.                                        --
--                                                                    --
-- Letters reach up without bound: `!≥ q` a strict wait of at least   --
-- `q`, `!> q` of more than `q`, `≥ q` and `> q` stretches in which   --
-- any operation may run, `e & S` the stretch `e` admitting only the  --
-- operations of `S`. Activity before, between and after operations  --
-- is allowed only by explicit stretches such as `≥ 0`, so the empty  --
-- word is not the greatest grade. A delay is graded by the wait of   --
-- at least its length, the delay zero by the empty word.             --
------------------------------------------------------------------------

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ)

open import Util.Equality

open import Syntax.Durations.NonNegativeRational using (ℚ≥0ᴰ; ℚ≥0ᵀ)
import Syntax.Grades.Traces.RunningTimes as RunningTimes

module Syntax.Grades.Example.Traces.Rigid.Rational.LeftSided
  (Op : Set) (n : ℕ) (code : Op → Fin n) (name : Fin n → Op)
  (name-code : ∀ o → name (code o) ≡ o) (code-name : ∀ c → code (name c) ≡ c)
  (running : RunningTimes.RunningTimes ℚ≥0ᵀ Op) where

open import Data.Fin.Subset using () renaming (⊤ to all; ⊥ to none)

open import Syntax.Grades using (Grade)
open import Syntax.Durations.Monus ℚ≥0ᵀ using (Carrier)
open import Syntax.Durations.Intervals ℚ≥0ᵀ using (⁻; ⁺) renaming (_∣_ to _∣ᶜ_)

open import Syntax.Grades.Example.Traces.Rigid.Rational.Base Op n code name name-code code-name running public

------------------------------------------------------------------------
-- Letters

Lower : Set
Lower = Expr lower

!≥_ !>_ ≥_ >_ : Carrier → Lower
!≥ d = str none (d ∣ᶜ ⁻)
!> d = str none (d ∣ᶜ ⁺)
≥ d  = str all (d ∣ᶜ ⁻)
> d  = str all (d ∣ᶜ ⁺)

infix 9 !≥_ !>_ ≥_ >_
infix 8 _&_

_&_ : Lower → OpSet → Lower
str _ e & S = str S e
e       & _ = e

------------------------------------------------------------------------
-- The grade

left-sided : Grade ℚ≥0ᴰ
left-sided = lowerᵍ
