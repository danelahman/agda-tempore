------------------------------------------------------------------------
-- The time-strict allowance relation, and its preorder structure.     --
--                                                                    --
-- `Traces.Allowance`'s `_≼ᵃ[ k ]_` banks budget *globally*: a delay   --
-- the bound offers anywhere may pay for work the run does anywhere    --
-- else. So a bound of `⌈ send ⌉ ∙ ⟨ 4 ⟩ ∙ ⌈ send ⌉` permits a run     --
-- that does its four ticks of work before the first transmission.     --
--                                                                    --
-- This relation forbids that. It is the same rules but for one: an    --
-- operation matched against the bound does not carry budget across    --
-- it.                                                                --
--                                                                    --
--   keep : s ≼ᵃᵗ[ 0 ] t  →  operation o s ≼ᵃᵗ[ k ] operation o t     --
--                                                                    --
-- Budget banked before a matched operation is discarded there, so the --
-- work a run does between two operations the bound names can only be  --
-- paid for by what the bound offers between the *same* two. Budget    --
-- still moves freely within such a segment.                          --
--                                                                    --
-- Everything else is unchanged -- the arithmetic helpers and the size --
-- measure are shared with the lenient order -- and `≼ᵃᵗ→≼ᵃ` records   --
-- that this is a restriction of it.                                  --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+[n∸m]≡n; m∸n+n≡m; +-∸-assoc)

open import Util.Equality

module Syntax.Grades.Traces.AllowanceTimed.Core (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺)

-- the arithmetic helpers and the size measure do not depend on the
-- rules, so they are the lenient order's

open import Syntax.Grades.Traces.Allowance.Core Op cost
  using (lem-swap; ∸-cancel; ≤-bump; size; size⁻; size-inj⁻)
  renaming (_≼ᵃ[_]_ to _≼ᵃ'[_]_; nil to nil'; keep to keep';
            skip-op to skip-op'; bank-delay to bank-delay';
            use-delay to use-delay'; use-op to use-op'; weaken to weaken')
  public

------------------------------------------------------------------------
-- The relation

infix 4 _≼ᵃᵗ[_]_

data _≼ᵃᵗ[_]_ : Trace → ℕ → Trace → Set where

  -- the empty run is permitted by every bound
  nil        : ∀ {k t}
             --------------
             → ε ≼ᵃᵗ[ k ] t

  -- an operation the bound names is permitted outright -- and the
  -- budget banked up to here does NOT cross the match
  keep       : ∀ {k o s t}
             → s ≼ᵃᵗ[ 0 ] t
             ---------------------------------------
             → operation o s ≼ᵃᵗ[ k ] operation o t

  -- one the bound names but the run does not perform is skipped
  skip-op    : ∀ {k o s t}
             → s ≼ᵃᵗ[ k ] t
             ----------------------------
             → s ≼ᵃᵗ[ k ] operation o t

  -- a delay of the bound is banked as budget, at its length
  bank-delay : ∀ {k e s t⁻}
             → s ≼ᵃᵗ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
             -----------------------------
             → s ≼ᵃᵗ[ k ] delay e t⁻

  -- spend budget on a delay the run takes
  use-delay  : ∀ {k d s⁻ t}
             → ∣ d ∣⁺ ≤ k
             → inj⁻ s⁻ ≼ᵃᵗ[ k ∸ ∣ d ∣⁺ ] t
             -----------------------------
             → delay d s⁻ ≼ᵃᵗ[ k ] t

  -- and on an operation the bound does not name
  use-op     : ∀ {k o s t}
             → cost o ≤ k
             → s ≼ᵃᵗ[ k ∸ cost o ] t
             -------------------------------
             → operation o s ≼ᵃᵗ[ k ] t

-- the order proper grants no budget to begin with

infix 4 _≼ᵃᵗ_

_≼ᵃᵗ_ : Trace → Trace → Set
s ≼ᵃᵗ t = s ≼ᵃᵗ[ 0 ] t

-- rewriting the budget along an equation

coe : ∀ {j k s t} → j ≡ k → s ≼ᵃᵗ[ j ] t → s ≼ᵃᵗ[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any budget)
--
-- Unchanged but for the matched-operation case, which now recurses at
-- budget zero -- which is where the induction already was.

mutual

  ≼ᵃᵗ-refl : ∀ {k} (s : Trace) → s ≼ᵃᵗ[ k ] s
  ≼ᵃᵗ-refl ε                = nil
  ≼ᵃᵗ-refl (operation o s)  = keep (≼ᵃᵗ-refl s)
  ≼ᵃᵗ-refl {k} (delay d s⁻) =
    bank-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼ᵃᵗ-refl⁻ s⁻))

  ≼ᵃᵗ-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼ᵃᵗ[ k ] inj⁻ s⁻
  ≼ᵃᵗ-refl⁻ ε⁻               = nil
  ≼ᵃᵗ-refl⁻ (operation⁻ o s) = keep (≼ᵃᵗ-refl s)

------------------------------------------------------------------------
-- Weakening: more budget is always fine
--
-- A matched operation discards the budget anyway, so that case has
-- nothing to weaken.

weaken : ∀ {j s t} (m : ℕ) → s ≼ᵃᵗ[ j ] t → s ≼ᵃᵗ[ j + m ] t
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
-- The matched-operation cases are where the two orders part: budget
-- reaching a match is discarded, so what crosses it has to be
-- re-weakened on the other side rather than carried.

≼ᵃᵗ-trans : ∀ {j k s t u} → s ≼ᵃᵗ[ j ] t → t ≼ᵃᵗ[ k ] u → s ≼ᵃᵗ[ j + k ] u
≼ᵃᵗ-trans nil                       _                       = nil
≼ᵃᵗ-trans (keep d1)                 (keep d2)               = keep (≼ᵃᵗ-trans d1 d2)
≼ᵃᵗ-trans {j} {k} (skip-op d1)      (keep d2)               =
  skip-op (coe (trans (+-assoc j 0 k) (cong (j +_) refl))
               (weaken k (≼ᵃᵗ-trans d1 d2)))
≼ᵃᵗ-trans d1                        (skip-op d2)            = skip-op (≼ᵃᵗ-trans d1 d2)
≼ᵃᵗ-trans {j} {k} d1                (bank-delay {e = e} d2) =
  bank-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᵃᵗ-trans d1 d2))
≼ᵃᵗ-trans {j} {k} (keep d1)         (use-op {o = o} p d2)   =
  use-op (≤-trans p (m≤n+m k j))
         (coe (trans (+-comm (k ∸ cost o) j) (sym (+-∸-assoc j p)))
              (weaken j (≼ᵃᵗ-trans d1 d2)))
≼ᵃᵗ-trans {j} {k} (skip-op d1)      (use-op {o = o} p d2)   =
  coe (trans (+-assoc j (k ∸ cost o) (cost o))
             (cong (j +_) (m∸n+n≡m p)))
      (weaken (cost o) (≼ᵃᵗ-trans d1 d2))
≼ᵃᵗ-trans {j} {k} (bank-delay {e = e} d1) (use-delay p d2)  =
  coe (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺))
             (cong (j +_) (m+[n∸m]≡n p)))
      (≼ᵃᵗ-trans d1 d2)
≼ᵃᵗ-trans {j} {k} (use-delay {d = d} p d1) d2               =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼ᵃᵗ-trans d1 d2))
≼ᵃᵗ-trans {j} {k} (use-op {o = o} p d1)    d2               =
  use-op (≤-trans p (m≤m+n j k))
         (coe (sym (+-∸-comm k p)) (≼ᵃᵗ-trans d1 d2))

------------------------------------------------------------------------
-- The time-strict order is a restriction of the lenient one
--
-- Every rule is the lenient rule; `keep` merely arrives with less
-- budget, which weakening restores.

≼ᵃᵗ→≼ᵃ : ∀ {k s t} → s ≼ᵃᵗ[ k ] t → s ≼ᵃ'[ k ] t
≼ᵃᵗ→≼ᵃ nil                = nil'
≼ᵃᵗ→≼ᵃ {k} (keep d)       = keep' (weaken' k (≼ᵃᵗ→≼ᵃ d))
≼ᵃᵗ→≼ᵃ (skip-op d)        = skip-op' (≼ᵃᵗ→≼ᵃ d)
≼ᵃᵗ→≼ᵃ (bank-delay d)     = bank-delay' (≼ᵃᵗ→≼ᵃ d)
≼ᵃᵗ→≼ᵃ (use-delay p d)    = use-delay' p (≼ᵃᵗ→≼ᵃ d)
≼ᵃᵗ→≼ᵃ (use-op p d)       = use-op' p (≼ᵃᵗ→≼ᵃ d)
