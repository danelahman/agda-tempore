------------------------------------------------------------------------
-- The slack-indexed coverage relation, and its preorder structure.    --
--                                                                    --
-- `s ≼ᶜ[ k ] t` reads: the run `t` covers the trace `s`, given `k`    --
-- units of slack already banked. Read as a guarantee `s` and an       --
-- elapsed run `t`:                                                   --
--                                                                    --
--   * every operation `s` names must genuinely occur in `t`, in       --
--     order (`keep`) -- it is never bought with time;                 --
--   * every delay `s` names is paid out of slack (`use-delay`), and   --
--     slack is banked from whatever `t` did that `s` did not name:    --
--     its unmatched operations at their execution time (`pay-op`)     --
--     and its delays at their length (`del-delay`);                   --
--   * and slack does not cross a match. `keep` recurses at slack      --
--     zero, so a delay `s` places between two operations it names is  --
--     paid only by what the run does between those same two.         --
--                                                                    --
-- Time discharges a demand for time; nothing discharges a demand for  --
-- an operation but the operation, and a demand for time is met only   --
-- where it is placed. This is the order a *guarantee* wants, and it   --
-- is deliberately not the converse of `Traces.Allowance`: there time  --
-- buys operations, which would let a run that merely idles discharge  --
-- a guarantee that a reading was taken.                              --
--                                                                    --
-- The relation is a preorder at the slacks: reflexive at any slack,   --
-- weakenable to more slack, and transitive with the slacks adding up. --
-- Everything derived from those laws -- the moves, the duration bound --
-- and the decision procedure -- lives in the sibling modules.         --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+[n∸m]≡n; m∸n+n≡m)

open import Util.Equality

module Syntax.Grades.Traces.Coverage.Core (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺)

-- the slack arithmetic and the size measure are shared with the other
-- order on traces

open import Syntax.Grades.Traces.Slack Op public

------------------------------------------------------------------------
-- The relation

infix 4 _≼ᶜ[_]_

data _≼ᶜ[_]_ : Trace → ℕ → Trace → Set where

  -- the empty trace demands nothing, so anything meets it
  nil       : ∀ {k t}
            -------------
            → ε ≼ᶜ[ k ] t

  -- a demanded operation is met by the same operation occurring -- and
  -- the slack banked up to here does NOT cross the match
  keep      : ∀ {k o s t}
            → s ≼ᶜ[ 0 ] t
            --------------------------------------
            → operation o s ≼ᶜ[ k ] operation o t

  -- an undemanded operation of the run is banked, at its execution time
  pay-op    : ∀ {k o s t}
            → s ≼ᶜ[ k + cost o ] t
            -------------------------
            → s ≼ᶜ[ k ] operation o t

  -- likewise an undemanded delay of the run, at its length
  del-delay : ∀ {k e s t⁻}
            → s ≼ᶜ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
            ----------------------------
            → s ≼ᶜ[ k ] delay e t⁻

  -- spend slack to meet a demanded delay
  use-delay : ∀ {k d s⁻ t}
            → ∣ d ∣⁺ ≤ k
            → inj⁻ s⁻ ≼ᶜ[ k ∸ ∣ d ∣⁺ ] t
            ----------------------------
            → delay d s⁻ ≼ᶜ[ k ] t

-- the order proper grants no slack to begin with

infix 4 _≼ᶜ_

_≼ᶜ_ : Trace → Trace → Set
s ≼ᶜ t = s ≼ᶜ[ 0 ] t

-- rewriting the slack along an equation

coe : ∀ {j k s t} → j ≡ k → s ≼ᶜ[ j ] t → s ≼ᶜ[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any slack)
--
-- A run covers itself: every operation it names is matched by the same
-- operation and every delay by the same delay, whose length the run has
-- just banked. The matched case recurses at slack zero, which is where
-- the induction already was.

mutual

  ≼ᶜ-refl : ∀ {k} (s : Trace) → s ≼ᶜ[ k ] s
  ≼ᶜ-refl ε                = nil
  ≼ᶜ-refl (operation o s)  = keep (≼ᶜ-refl s)
  ≼ᶜ-refl {k} (delay d s⁻) =
    del-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼ᶜ-refl⁻ s⁻))

  ≼ᶜ-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼ᶜ[ k ] inj⁻ s⁻
  ≼ᶜ-refl⁻ ε⁻               = nil
  ≼ᶜ-refl⁻ (operation⁻ o s) = keep (≼ᶜ-refl s)

------------------------------------------------------------------------
-- Weakening: more slack is always fine
--
-- The `keep` case is now immediate: its premise does not mention the
-- slack being weakened.

weaken : ∀ {j s t} (m : ℕ) → s ≼ᶜ[ j ] t → s ≼ᶜ[ j + m ] t
weaken m nil                          = nil
weaken m (keep d)                     = keep d
weaken {j} m (pay-op {o = o} d)       =
  pay-op (coe (lem-swap j (cost o) m) (weaken m d))
weaken {j} m (del-delay {e = e} d)    =
  del-delay (coe (lem-swap j ∣ e ∣⁺ m) (weaken m d))
weaken {j} m (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n j m))
            (coe (sym (+-∸-comm m p)) (weaken m d'))

-- dropping an operation of the run without spending what it banks

del-op : ∀ {k o s t} → s ≼ᶜ[ k ] t → s ≼ᶜ[ k ] operation o t
del-op {k} {o} d = pay-op (weaken (cost o) d)

------------------------------------------------------------------------
-- Transitivity: the slacks add up
--
-- The awkward case is `pay-op` against `keep`: the middle run's matched
-- operation resets the slack, so the inductive hypothesis lands at
-- `(j + cost o) + 0` and has to be weakened by `k` before it can be
-- re-associated.

≼ᶜ-trans : ∀ {j k s t u} → s ≼ᶜ[ j ] t → t ≼ᶜ[ k ] u → s ≼ᶜ[ j + k ] u
≼ᶜ-trans nil _ = nil
-- the demand keeps an operation, which the middle run has: both sides
-- of the match are at slack zero, so the composite is too
≼ᶜ-trans (keep d1) (keep d2) = keep (≼ᶜ-trans d1 d2)
≼ᶜ-trans {j} {k} (keep d1) (pay-op {o = o} d2) =
  pay-op (coe (sym (+-assoc j k (cost o))) (≼ᶜ-trans {j} (keep d1) d2))
≼ᶜ-trans {j} {k} (keep d1) (del-delay {e = e} d2) =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᶜ-trans {j} (keep d1) d2))
-- the demand banks an operation of the middle run, which the run must
-- therefore also have; the match on the right resets the slack, so what
-- the hypothesis gives has to be weakened back up
≼ᶜ-trans {j} {k} (pay-op {o = o} d1) (keep d2) =
  pay-op (coe (lem-swap j (cost o) k)
              (weaken k (coe (+-identityʳ (j + cost o)) (≼ᶜ-trans d1 d2))))
≼ᶜ-trans {j} {k} (pay-op d1) (pay-op {o = o} d2) =
  pay-op (coe (sym (+-assoc j k (cost o))) (≼ᶜ-trans (pay-op d1) d2))
≼ᶜ-trans {j} {k} (pay-op d1) (del-delay {e = e} d2) =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᶜ-trans (pay-op d1) d2))
-- the demand banks a delay of the middle run
≼ᶜ-trans {j} {k} (del-delay {e = e} d1) (use-delay p d2) =
  coe (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺)) (cong (j +_) (m+[n∸m]≡n p)))
      (≼ᶜ-trans d1 d2)
≼ᶜ-trans {j} {k} (del-delay d1) (pay-op {o = o} d2) =
  pay-op (coe (sym (+-assoc j k (cost o))) (≼ᶜ-trans (del-delay d1) d2))
≼ᶜ-trans {j} {k} (del-delay d1) (del-delay {e = f} d2) =
  del-delay (coe (sym (+-assoc j k ∣ f ∣⁺)) (≼ᶜ-trans (del-delay d1) d2))
-- the demand spends slack on its own leading delay
≼ᶜ-trans {j} {k} (use-delay {d = d} p d1) D2 =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼ᶜ-trans d1 D2))

