------------------------------------------------------------------------
-- The slack-indexed sub-trace relation, and its preorder structure.   --
--                                                                     --
-- `s ≼[ k ] t` reads: the trace `s` fits inside the schedule `t` given --
-- `k` extra units of slack to spend. Slack is created by absorbing a   --
-- delay of the right-hand trace and spent on a leading delay or        --
-- operation of the left-hand one, at that operation's execution time.  --
--                                                                     --
-- The relation is a preorder at the slacks: reflexive at any slack,    --
-- weakenable to more slack, and transitive with the slacks adding up.  --
-- Everything derived from those laws -- the moves that build sub-trace --
-- proofs, and the decision procedure -- lives in the sibling modules.  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+n∸n≡m; m+[n∸m]≡n; m∸n+n≡m; +-monoʳ-≤; ∸-+-assoc; +-∸-assoc)

open import Util.Equality

-- Sub-trace orders are parameterised by a set `Op` of operation names
-- and by the map `cost` giving each operation its execution time.

module Syntax.Grades.Traces.Subtrace.Core (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺)

------------------------------------------------------------------------
-- Small arithmetic helpers

-- swapping the two trailing summands

lem-swap : (a b c : ℕ) → (a + b) + c ≡ (a + c) + b
lem-swap a b c =
  trans (+-assoc a b c)
        (trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b)))

-- cancelling a common summand under truncated subtraction

∸-cancel : (m d e : ℕ) → (m + d) ∸ (d + e) ≡ m ∸ e
∸-cancel m d e =
  trans (sym (∸-+-assoc (m + d) d e)) (cong (_∸ e) (m+n∸n≡m m d))

-- monotonicity used when bumping a leading delay

≤-bump : (D E m : ℕ) → E ≤ m → D + E ≤ m + D
≤-bump D E m E≤m = subst (D + E ≤_) (+-comm D m) (+-monoʳ-≤ D E≤m)

------------------------------------------------------------------------
-- A structural size measure on traces
--
-- Each node counts as one; a leading delay counts the size of its
-- delay-free-headed continuation. This measure drives the fuelled
-- decision procedure in `Subtrace.Decidable`: every recursive call
-- strictly decreases it.

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

------------------------------------------------------------------------
-- The slack-indexed sub-trace relation

infix 4 _≼[_]_

data _≼[_]_ : Trace → ℕ → Trace → Set where

  -- the empty trace lies below anything: drop all operations of `t` and
  -- decrease all of its delays to zero
  nil       : ∀ {k t}
            ------------
            → ε ≼[ k ] t

  -- keep a leading operation (no leading delay on either side)
  keep      : ∀ {k o s t}
            → s ≼[ k ] t
            ------------------------------------
            → operation o s ≼[ k ] operation o t

  -- delete the leading operation of the right-hand trace
  del-op    : ∀ {k o s t}
            → s ≼[ k ] t
            ------------------------
            → s ≼[ k ] operation o t

  -- absorb the leading delay of the right-hand trace into the slack;
  -- this is what lets several right-hand delays collapse together as the
  -- operations between them are deleted
  del-delay : ∀ {k e s t⁻}
            → s ≼[ k + ∣ e ∣⁺ ] inj⁻ t⁻
            ---------------------------
            → s ≼[ k ] delay e t⁻

  -- spend slack to cover the leading operation of the left-hand trace,
  -- at the execution time that operation takes
  use-op    : ∀ {k o s t}
            → cost o ≤ k
            → s ≼[ k ∸ cost o ] t
            ------------------------
            → operation o s ≼[ k ] t

  -- spend slack to cover the leading delay of the left-hand trace
  use-delay : ∀ {k d s⁻ t}
            → ∣ d ∣⁺ ≤ k
            → inj⁻ s⁻ ≼[ k ∸ ∣ d ∣⁺ ] t
            ---------------------------
            → delay d s⁻ ≼[ k ] t

-- the sub-trace order proper grants no extra slack

infix 4 _≼_

_≼_ : Trace → Trace → Set
s ≼ t = s ≼[ 0 ] t

-- rewriting the slack along an equation (the endpoints are fixed, so
-- this is just transport and avoids leaving them as metavariables)

coe : ∀ {j k s t} → j ≡ k → s ≼[ j ] t → s ≼[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any slack)

mutual

  ≼-refl : ∀ {k} (s : Trace) → s ≼[ k ] s
  ≼-refl ε                 = nil
  ≼-refl (operation o s)   = keep (≼-refl s)
  ≼-refl {k} (delay d s⁻)  =
    del-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼-refl⁻ s⁻))

  ≼-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼[ k ] inj⁻ s⁻
  ≼-refl⁻ ε⁻               = nil
  ≼-refl⁻ (operation⁻ o s) = keep (≼-refl s)

------------------------------------------------------------------------
-- Weakening: more slack is always fine

weaken : ∀ {j s t} (m : ℕ) → s ≼[ j ] t → s ≼[ j + m ] t
weaken m nil                       = nil
weaken m (keep d)                  = keep (weaken m d)
weaken m (del-op d)                = del-op (weaken m d)
weaken {j} m (del-delay {e = e} d) =
  del-delay (coe (lem-swap j ∣ e ∣⁺ m) (weaken m d))
weaken {j} m (use-op p d') =
  use-op (≤-trans p (m≤m+n j m))
         (coe (sym (+-∸-comm m p)) (weaken m d'))
weaken {j} m (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n j m))
            (coe (sym (+-∸-comm m p)) (weaken m d'))

------------------------------------------------------------------------
-- Transitivity: the slacks add up

≼-trans : ∀ {j k s t u} → s ≼[ j ] t → t ≼[ k ] u → s ≼[ j + k ] u
≼-trans nil                       _                       = nil
-- left factor keeps an operation
≼-trans (keep d1)        (keep d2)                        = keep (≼-trans d1 d2)
≼-trans {j} {k} (keep d1) (use-op p d2)                   =
  use-op (≤-trans p (m≤n+m k j))
         (coe (sym (+-∸-assoc j p)) (≼-trans d1 d2))
≼-trans (keep d1)        (del-op d2)                      = del-op (≼-trans (keep d1) d2)
≼-trans {j} {k} (keep d1) (del-delay {e = e} d2)          =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺))
            (≼-trans (keep d1) d2))
-- left factor deletes an operation of the middle trace
≼-trans (del-op d1)      (keep d2)                        = del-op (≼-trans d1 d2)
≼-trans {j} {k} (del-op d1) (use-op {o = o} p d2)         =
  coe (trans (+-assoc j (k ∸ cost o) (cost o))
             (cong (j +_) (m∸n+n≡m p)))
      (weaken (cost o) (≼-trans d1 d2))
≼-trans (del-op d1)      (del-op d2)                      = del-op (≼-trans (del-op d1) d2)
≼-trans {j} {k} (del-op d1) (del-delay {e = e} d2)        =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺))
            (≼-trans (del-op d1) d2))
-- left factor absorbs the leading delay of the middle trace
≼-trans {j} {k} (del-delay {e = e} d1) (use-delay p d2)   =
  coe
        (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺)) (cong (j +_) (m+[n∸m]≡n p)))
        (≼-trans d1 d2)
≼-trans (del-delay d1)   (del-op d2)                      = del-op (≼-trans (del-delay d1) d2)
≼-trans {j} {k} (del-delay d1) (del-delay {e = f} d2)     =
  del-delay (coe (sym (+-assoc j k ∣ f ∣⁺))
            (≼-trans (del-delay d1) d2))
-- left factor spends slack on its own leading operation or delay
≼-trans {j} {k} (use-op p d1) D2                          =
  use-op (≤-trans p (m≤m+n j k))
         (coe (sym (+-∸-comm k p)) (≼-trans d1 D2))
≼-trans {j} {k} (use-delay {d = d} p d1) D2               =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼-trans d1 D2))
