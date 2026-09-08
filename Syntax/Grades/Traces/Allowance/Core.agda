------------------------------------------------------------------------
-- The budget-indexed allowance relation, and its preorder structure.  --
--                                                                    --
-- `s ≼ᵃ[ k ] t` reads: the bound `t` permits the run `s`, given `k`    --
-- units of budget already banked. Read as a bound `t` and a run `s`:   --
--                                                                    --
--   * an operation the bound names is permitted outright (`keep`),     --
--     and one the bound does not name is paid for out of budget, at    --
--     its execution time (`use-op`);                                   --
--   * a delay the run takes is paid for out of budget (`use-delay`);   --
--   * budget comes from the bound's delays, at their length            --
--     (`bank-delay`), and from nowhere else: an operation the bound    --
--     names but the run does not perform is simply skipped, freeing    --
--     nothing (`skip-op`);                                            --
--   * and budget does not cross a match. `keep` recurses at budget     --
--     zero, so what the bound offers before an operation it names is   --
--     spent before that operation or not at all.                      --
--                                                                    --
-- So a bound limits what happens, how long it takes, and *when* its    --
-- slack is available: its operations say which effects are permitted   --
-- outright, and each stretch of delay is a budget for the work the run --
-- does in the same stretch. Going up the order, an operation turns     --
-- into a delay long enough to cover it and a delay grows.             --
--                                                                    --
-- The relation is a preorder at the budgets: reflexive at any budget,  --
-- weakenable to more budget, and transitive with the budgets adding    --
-- up. Everything derived from those laws -- the moves that build       --
-- allowance proofs, the duration bound, and the decision procedure --  --
-- lives in the sibling modules.                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+n∸n≡m; m+[n∸m]≡n; m∸n+n≡m; +-monoʳ-≤; ∸-+-assoc; +-∸-assoc)

open import Util.Equality

-- The allowance order is parameterised by a set `Op` of operation names
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
-- The relation

infix 4 _≼ᵃ[_]_

data _≼ᵃ[_]_ : Trace → ℕ → Trace → Set where

  -- the empty run is permitted by every bound
  nil        : ∀ {k t}
             -------------
             → ε ≼ᵃ[ k ] t

  -- an operation the bound names is permitted outright -- and the
  -- budget banked up to here does NOT cross the match
  keep       : ∀ {k o s t}
             → s ≼ᵃ[ 0 ] t
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

-- rewriting the budget along an equation (the endpoints are fixed, so
-- this is just transport and avoids leaving them as metavariables)

coe : ∀ {j k s t} → j ≡ k → s ≼ᵃ[ j ] t → s ≼ᵃ[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any budget)
--
-- Every operation of the run is named by the bound and every delay is
-- covered by the same delay, so nothing is spent -- and the matched
-- operations recurse at budget zero, which is where the induction
-- already was.

mutual

  ≼ᵃ-refl : ∀ {k} (s : Trace) → s ≼ᵃ[ k ] s
  ≼ᵃ-refl ε                = nil
  ≼ᵃ-refl (operation o s)  = keep (≼ᵃ-refl s)
  ≼ᵃ-refl {k} (delay d s⁻) =
    bank-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼ᵃ-refl⁻ s⁻))

  ≼ᵃ-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼ᵃ[ k ] inj⁻ s⁻
  ≼ᵃ-refl⁻ ε⁻               = nil
  ≼ᵃ-refl⁻ (operation⁻ o s) = keep (≼ᵃ-refl s)

------------------------------------------------------------------------
-- Weakening: more budget is always fine
--
-- A matched operation discards the budget anyway, so that case has
-- nothing to weaken.

weaken : ∀ {j s t} (m : ℕ) → s ≼ᵃ[ j ] t → s ≼ᵃ[ j + m ] t
weaken m nil                          = nil
weaken m (keep d)                     = keep d
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
-- Transitivity: the budgets add up
--
-- The matched-operation cases are where budget is discarded, so what
-- crosses a match has to be re-weakened on the other side rather than
-- carried.

≼ᵃ-trans : ∀ {j k s t u} → s ≼ᵃ[ j ] t → t ≼ᵃ[ k ] u → s ≼ᵃ[ j + k ] u
≼ᵃ-trans nil                       _                       = nil
≼ᵃ-trans (keep d1)                 (keep d2)               = keep (≼ᵃ-trans d1 d2)
≼ᵃ-trans {j} {k} (skip-op d1)      (keep d2)               =
  skip-op (coe (trans (+-assoc j 0 k) (cong (j +_) refl))
               (weaken k (≼ᵃ-trans d1 d2)))
≼ᵃ-trans d1                        (skip-op d2)            = skip-op (≼ᵃ-trans d1 d2)
≼ᵃ-trans {j} {k} d1                (bank-delay {e = e} d2) =
  bank-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᵃ-trans d1 d2))
≼ᵃ-trans {j} {k} (keep d1)         (use-op {o = o} p d2)   =
  use-op (≤-trans p (m≤n+m k j))
         (coe (trans (+-comm (k ∸ cost o) j) (sym (+-∸-assoc j p)))
              (weaken j (≼ᵃ-trans d1 d2)))
≼ᵃ-trans {j} {k} (skip-op d1)      (use-op {o = o} p d2)   =
  coe (trans (+-assoc j (k ∸ cost o) (cost o))
             (cong (j +_) (m∸n+n≡m p)))
      (weaken (cost o) (≼ᵃ-trans d1 d2))
≼ᵃ-trans {j} {k} (bank-delay {e = e} d1) (use-delay p d2)  =
  coe (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺))
             (cong (j +_) (m+[n∸m]≡n p)))
      (≼ᵃ-trans d1 d2)
≼ᵃ-trans {j} {k} (use-delay {d = d} p d1) d2               =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼ᵃ-trans d1 d2))
≼ᵃ-trans {j} {k} (use-op {o = o} p d1)    d2               =
  use-op (≤-trans p (m≤m+n j k))
         (coe (sym (+-∸-comm k p)) (≼ᵃ-trans d1 d2))
