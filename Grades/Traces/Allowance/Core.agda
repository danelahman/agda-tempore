--------------------------------------------------------------------------
-- The budget-indexed allowance relation, and its preorder structure.   --
--                                                                      --
-- `s ≼ᵃ[ k ] t` reads: the bound `t` permits the run `s`, given a      --
-- budget `k` already banked:                                           --
--                                                                      --
--   * an operation the bound names is permitted outright (`keep`),     --
--     and one the bound does not name is paid for out of budget, at    --
--     its running time (`use-op`);                                     --
--   * a delay the run takes is paid for out of budget (`use-delay`);   --
--   * budget comes from the bound's delays, at their length            --
--     (`bank-delay`), and from nowhere else: an operation the bound    --
--     names but the run does not perform is skipped, freeing           --
--     nothing (`skip-op`);                                             --
--   * and budget does not cross a match. `keep` recurses at budget     --
--     zero, so what the bound offers before an operation it names is   --
--     spent before that operation or not at all.                       --
--                                                                      --
-- So a bound limits what happens, how long it takes, and when its      --
-- slack is available: its operations say which effects are permitted   --
-- outright, and each stretch of delay is a budget for the work the run --
-- does in the same stretch. Going up the order, an operation turns     --
-- into a delay long enough to cover it and a delay grows.              --
--                                                                      --
-- The relation is a preorder at the budgets: reflexive at any budget,  --
-- weakenable to more budget, and transitive with the budgets adding    --
-- up. The moves that build allowance proofs, the duration bound and    --
-- the decision procedure are in the sibling modules.                   --
--------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc)

open import Util.Equality

-- The allowance order is parameterised by a set `Op` of operation names
-- and by the map `costʰⁱ` giving each operation the most time it can
-- take, that being what a bound must budget for.

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Allowance.Core
  {D : Duration} (T : TimeDomain D) (Op : Set) (costʰⁱ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Base T Op

-- the slack arithmetic and the size measure, shared by both orders on
-- traces

open import Grades.Traces.Slack T Op public

------------------------------------------------------------------------
-- The relation

infix 4 _≼ᵃ[_]_

data _≼ᵃ[_]_ : Trace → Carrier → Trace → Set where

  -- the empty run is permitted by every bound
  nil        : ∀ {k t}
             -------------
             → ε ≼ᵃ[ k ] t

  -- an operation the bound names is permitted outright; the budget
  -- banked so far does not cross the match
  keep       : ∀ {k o s t}
             → s ≼ᵃ[ 0ᴰ ] t
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

  -- and on an operation the bound does not name, at its running time
  use-op     : ∀ {k o s t}
             → costʰⁱ o ≤ k
             → s ≼ᵃ[ k ∸ costʰⁱ o ] t
             ------------------------------
             → operation o s ≼ᵃ[ k ] t

-- the allowance order proper grants no budget to begin with

infix 4 _≼ᵃ_

_≼ᵃ_ : Trace → Trace → Set
s ≼ᵃ t = s ≼ᵃ[ 0ᴰ ] t

-- rewriting the budget along an equation, the endpoints fixed so that
-- they are not left as metavariables

coe : ∀ {j k s t} → j ≡ k → s ≼ᵃ[ j ] t → s ≼ᵃ[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any budget)
--
-- Every operation of the run is named by the bound and every delay
-- covered by the same delay, so nothing is spent; matched operations
-- recurse at budget zero, where the induction already is.

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
-- Weakening to more budget
--
-- A matched operation discards the budget, so that case has nothing to
-- weaken.

weaken : ∀ {j s t} (m : Carrier) → s ≼ᵃ[ j ] t → s ≼ᵃ[ j + m ] t
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
-- Budget is discarded at a match, so what crosses one is weakened
-- again on the other side, not carried.

≼ᵃ-trans : ∀ {j k s t u} → s ≼ᵃ[ j ] t → t ≼ᵃ[ k ] u → s ≼ᵃ[ j + k ] u
≼ᵃ-trans nil                       _                       = nil
≼ᵃ-trans (keep d1)                 (keep d2)               =
  keep (coe (+-identityʳ 0ᴰ) (≼ᵃ-trans d1 d2))
≼ᵃ-trans {j} {k} (skip-op d1)      (keep d2)               =
  skip-op (coe (trans (+-assoc j 0ᴰ k) (cong (j +_) (+-identityˡ k)))
               (weaken k (≼ᵃ-trans d1 d2)))
≼ᵃ-trans d1                        (skip-op d2)            = skip-op (≼ᵃ-trans d1 d2)
≼ᵃ-trans {j} {k} d1                (bank-delay {e = e} d2) =
  bank-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᵃ-trans d1 d2))
≼ᵃ-trans {j} {k} (keep d1)         (use-op {o = o} p d2)   =
  use-op (≤-trans p (m≤n+m k j))
         (coe (trans (+-comm (k ∸ costʰⁱ o) j) (sym (+-∸-assoc j p)))
              (weaken j (coe (+-identityˡ (k ∸ costʰⁱ o)) (≼ᵃ-trans d1 d2))))
≼ᵃ-trans {j} {k} (skip-op d1)      (use-op {o = o} p d2)   =
  coe (trans (+-assoc j (k ∸ costʰⁱ o) (costʰⁱ o))
             (cong (j +_) (m∸n+n≡m p)))
      (weaken (costʰⁱ o) (≼ᵃ-trans d1 d2))
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
