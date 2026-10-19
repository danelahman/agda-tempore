------------------------------------------------------------------------
-- The slack arithmetic the trace orders share.                        --
--                                                                    --
-- Both orders on timed traces carry a duration of banked time        --
-- and shuffle it about as they walk the two traces, and both are      --
-- decided by recursion on a fuel budget bounding the combined size of  --
-- those traces. None of that depends on the rules, so it is collected  --
-- here rather than restated in each.                                  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc)

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Traces.Slack {D : Duration} (T : TimeDomain D) (Op : Set) where

open import Syntax.Grades.Traces.Base T Op

open import Syntax.Durations.Monus T as M using (Carrier; ∸-+-assoc)
open M.Notation

------------------------------------------------------------------------
-- Small arithmetic helpers

-- swapping the two trailing summands

lem-swap : (a b c : Carrier) → (a + b) + c ≡ (a + c) + b
lem-swap a b c =
  trans (+-assoc a b c)
        (trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b)))

-- cancelling a common summand under truncated subtraction

∸-cancel : (m d e : Carrier) → (m + d) ∸ (d + e) ≡ m ∸ e
∸-cancel m d e =
  trans (sym (∸-+-assoc (m + d) d e)) (cong (_∸ e) (m+n∸n≡m m d))

-- monotonicity used when bumping a leading delay

≤-bump : (D E m : Carrier) → E ≤ m → D + E ≤ m + D
≤-bump D E m E≤m = subst (D + E ≤_) (+-comm D m) (+-monoʳ-≤ D E≤m)

------------------------------------------------------------------------
-- A structural size measure on traces
--
-- Each node counts as one; a leading delay counts the size of its
-- delay-free-headed continuation. Every rule of either order strictly
-- decreases the combined size of the two traces, which is what fuels
-- the decision procedures.

mutual

  size  : Trace  → ℕ
  size ε               = 0
  size (operation o t) = suc (size t)
  size (delay d t⁻)    = suc (size⁻ t⁻)

  size⁻ : Trace⁻ → ℕ
  size⁻ ε⁻               = 0
  size⁻ (operation⁻ o t) = suc (size t)

-- the delay-free injection preserves the size

size-inj⁻ : (t⁻ : Trace⁻) → size (inj⁻ t⁻) ≡ size⁻ t⁻
size-inj⁻ ε⁻               = refl
size-inj⁻ (operation⁻ o t) = refl
