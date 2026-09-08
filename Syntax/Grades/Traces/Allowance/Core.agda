------------------------------------------------------------------------
-- The slack-indexed allowance relation, and its preorder structure.   --
--                                                                     --
-- `s ≼ᵃ[ k ] t` reads: the bound `t` permits the run `s`, given `k`    --
-- units of budget already banked. Read as a bound `t` and a run `s`:   --
--                                                                     --
--   * an operation the bound names is permitted outright (`keep`),     --
--     and one the bound does not name is paid for out of budget, at    --
--     its execution time (`use-op`);                                   --
--   * a delay the run takes is paid for out of budget (`use-delay`);   --
--   * budget comes from the bound's delays, at their length            --
--     (`bank-delay`), and from nowhere else: an operation the bound    --
--     names but the run does not perform is simply skipped, freeing    --
--     nothing (`skip-op`).                                            --
--                                                                     --
-- So a bound limits both what happens and how long it takes: its       --
-- operations say which effects are permitted outright, and its delays  --
-- are a budget that the run's own idling and its unnamed operations    --
-- draw on. Going up the order, operations turn into delays long        --
-- enough to cover them and delays grow.                                --
--                                                                     --
-- The relation is a preorder at the slacks: reflexive at any slack,    --
-- weakenable to more slack, and transitive with the slacks adding up.  --
-- Everything derived from those laws -- the moves that build           --
-- allowance proofs, the duration bound, and the decision procedure --  --
-- lives in the sibling modules.                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+n∸n≡m; m+[n∸m]≡n; m∸n+n≡m; +-monoʳ-≤; ∸-+-assoc; +-∸-assoc)

open import Util.Equality

-- Allowance orders are parameterised by a set `Op` of operation names
-- and by the map `cost` giving each operation its execution time.

module Syntax.Grades.Traces.Allowance.Core (Op : Set) (cost : Op → ℕ) where

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
-- decision procedure in `Allowance.Decidable`: every rule strictly
-- decreases the combined size of the two traces.

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
-- The slack-indexed allowance relation

infix 4 _≼ᵃ[_]_

data _≼ᵃ[_]_ : Trace → ℕ → Trace → Set where

  -- the empty run is permitted by every bound
  nil        : ∀ {k t}
             -------------
             → ε ≼ᵃ[ k ] t

  -- an operation the bound names is permitted outright
  keep       : ∀ {k o s t}
             → s ≼ᵃ[ k ] t
             --------------------------------------
             → operation o s ≼ᵃ[ k ] operation o t

  -- one the bound names but the run does not perform is skipped, and
  -- frees nothing: a bound's operations are permissions, not budget
  skip-op    : ∀ {k o s t}
             → s ≼ᵃ[ k ] t
             ---------------------------
             → s ≼ᵃ[ k ] operation o t

  -- a delay of the bound is banked as budget, at its length
  bank-delay : ∀ {k e s t⁻}
             → s ≼ᵃ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
             ----------------------------
             → s ≼ᵃ[ k ] delay e t⁻

  -- spend budget on a delay the run takes
  use-delay  : ∀ {k d s⁻ t}
             → ∣ d ∣⁺ ≤ k
             → inj⁻ s⁻ ≼ᵃ[ k ∸ ∣ d ∣⁺ ] t
             ----------------------------
             → delay d s⁻ ≼ᵃ[ k ] t

  -- and on an operation the bound does not name, at its execution time
  use-op     : ∀ {k o s t}
             → cost o ≤ k
             → s ≼ᵃ[ k ∸ cost o ] t
             ------------------------------
             → operation o s ≼ᵃ[ k ] t

-- the allowance order proper grants no budget to begin with

infix 4 _≼ᵃ_

_≼ᵃ_ : Trace → Trace → Set
s ≼ᵃ t = s ≼ᵃ[ 0 ] t

-- rewriting the slack along an equation (the endpoints are fixed, so
-- this is just transport and avoids leaving them as metavariables)

coe : ∀ {j k s t} → j ≡ k → s ≼ᵃ[ j ] t → s ≼ᵃ[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any slack)
--
-- Every operation of the run is named by the bound and every delay is
-- covered by the same delay, so nothing is spent.

mutual

  ≼ᵃ-refl : ∀ {k} (s : Trace) → s ≼ᵃ[ k ] s
  ≼ᵃ-refl ε                 = nil
  ≼ᵃ-refl (operation o s)   = keep (≼ᵃ-refl s)
  ≼ᵃ-refl {k} (delay d s⁻)  =
    bank-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼ᵃ-refl⁻ s⁻))

  ≼ᵃ-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼ᵃ[ k ] inj⁻ s⁻
  ≼ᵃ-refl⁻ ε⁻               = nil
  ≼ᵃ-refl⁻ (operation⁻ o s) = keep (≼ᵃ-refl s)

------------------------------------------------------------------------
-- Weakening: more budget is always fine

weaken : ∀ {j s t} (m : ℕ) → s ≼ᵃ[ j ] t → s ≼ᵃ[ j + m ] t
weaken m nil                          = nil
weaken m (keep d)                     = keep (weaken m d)
weaken m (skip-op d)                  = skip-op (weaken m d)
weaken {j} m (bank-delay {e = e} d)   =
  bank-delay (coe (lem-swap j ∣ e ∣⁺ m) (weaken m d))
weaken {j} m (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n j m))
            (coe (sym (+-∸-comm m p)) (weaken m d'))
weaken {j} m (use-op {o = o} p d')    =
  use-op (≤-trans p (m≤m+n j m))
         (coe (sym (+-∸-comm m p)) (weaken m d'))

------------------------------------------------------------------------
-- Transitivity: the slacks add up

≼ᵃ-trans : ∀ {j k s t u} → s ≼ᵃ[ j ] t → t ≼ᵃ[ k ] u → s ≼ᵃ[ j + k ] u
-- the run does nothing, so any bound permits it
≼ᵃ-trans nil                       _                        = nil
-- the middle bound names the operation, and so does the outer one
≼ᵃ-trans (keep d1)                 (keep d2)                = keep (≼ᵃ-trans d1 d2)
-- the run skipped it, and the outer bound goes on naming it
≼ᵃ-trans (skip-op d1)              (keep d2)                = skip-op (≼ᵃ-trans d1 d2)
-- the outer bound offers an operation neither of the others uses
≼ᵃ-trans {j} {k} d1                (skip-op d2)             =
  skip-op (≼ᵃ-trans d1 d2)
-- the outer bound offers a delay, which only adds budget
≼ᵃ-trans {j} {k} d1                (bank-delay {e = e} d2)  =
  bank-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᵃ-trans d1 d2))
-- the middle bound's operation is paid for by the outer one's budget,
-- so the run's own copy of it is paid for out of the same budget
≼ᵃ-trans {j} {k} (keep d1)         (use-op {o = o} p d2)    =
  use-op (≤-trans p (m≤n+m k j))
         (coe (sym (+-∸-assoc j p)) (≼ᵃ-trans d1 d2))
-- the run skipped that operation anyway, so the budget spent on it is
-- simply not needed
≼ᵃ-trans {j} {k} (skip-op d1)      (use-op {o = o} p d2)    =
  coe (trans (+-assoc j (k ∸ cost o) (cost o))
             (cong (j +_) (m∸n+n≡m p)))
      (weaken (cost o) (≼ᵃ-trans d1 d2))
-- the middle bound's delay is banked by the run and spent by the outer
-- bound, and the two amounts cancel
≼ᵃ-trans {j} {k} (bank-delay {e = e} d1) (use-delay p d2)   =
  coe (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺))
             (cong (j +_) (m+[n∸m]≡n p)))
      (≼ᵃ-trans d1 d2)
-- what the run spends, it spends against the sum of the two budgets
≼ᵃ-trans {j} {k} (use-delay {d = d} p d1) d2                =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼ᵃ-trans d1 d2))
≼ᵃ-trans {j} {k} (use-op {o = o} p d1)    d2                =
  use-op (≤-trans p (m≤m+n j k))
         (coe (sym (+-∸-comm k p)) (≼ᵃ-trans d1 d2))
