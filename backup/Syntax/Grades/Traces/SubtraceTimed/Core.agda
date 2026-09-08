------------------------------------------------------------------------
-- The time-strict sub-trace relation, and its preorder structure.     --
--                                                                     --
-- `Traces.Subtrace`'s `_≼[ k ]_` banks slack *globally*: time earned   --
-- anywhere in the run may pay a delay demanded anywhere else. So a     --
-- demand for `read · ⟨ 2 ⟩ · send` is met by a run that stores before  --
-- the read, the store's execution time paying for a delay the demand   --
-- places after it.                                                    --
--                                                                     --
-- This relation forbids that. It is the same rules but for one: a      --
-- matched operation does not carry slack across it.                   --
--                                                                     --
--   keep : s ≼ᵗ[ 0 ] t  →  operation o s ≼ᵗ[ k ] operation o t        --
--                                                                     --
-- Slack banked before a matched operation is discarded there, so the   --
-- delays a demand places between two of its operations can only be     --
-- paid by what the run does between the *same* two operations. Time    --
-- still moves freely within such a segment -- an unmatched operation   --
-- between the read and the send does pay for the `⟨ 2 ⟩` -- which is   --
-- the point: it is banking across a match that is ruled out, not       --
-- banking as such.                                                    --
--                                                                     --
-- Everything else is unchanged, and `≼ᵗ→≼` records that this is a      --
-- restriction of the original: every time-strict derivation is a       --
-- sub-trace derivation.                                               --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+[n∸m]≡n; +-monoʳ-≤)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceTimed.Core (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺)

open import Syntax.Grades.Traces.Subtrace.Core Op cost
  using ()
  renaming (_≼[_]_ to _≼ˢ[_]_; nil to nilˢ; keep to keepˢ; pay-op to pay-opˢ;
            del-delay to del-delayˢ; use-delay to use-delayˢ;
            weaken to weakenˢ; coe to coeˢ)

------------------------------------------------------------------------
-- Small arithmetic helper: swapping the two trailing summands

lem-swap : (a b c : ℕ) → (a + b) + c ≡ (a + c) + b
lem-swap a b c =
  trans (+-assoc a b c)
        (trans (cong (a +_) (+-comm b c)) (sym (+-assoc a c b)))

------------------------------------------------------------------------
-- The relation

infix 4 _≼ᵗ[_]_

data _≼ᵗ[_]_ : Trace → ℕ → Trace → Set where

  -- the empty trace demands nothing, so anything meets it
  nil       : ∀ {k t}
            -------------
            → ε ≼ᵗ[ k ] t

  -- a demanded operation is met by the same operation occurring -- and
  -- the slack banked up to here does NOT cross the match
  keep      : ∀ {k o s t}
            → s ≼ᵗ[ 0 ] t
            --------------------------------------
            → operation o s ≼ᵗ[ k ] operation o t

  -- an undemanded operation of the run is banked, at its execution time
  pay-op    : ∀ {k o s t}
            → s ≼ᵗ[ k + cost o ] t
            -------------------------
            → s ≼ᵗ[ k ] operation o t

  -- likewise an undemanded delay of the run, at its length
  del-delay : ∀ {k e s t⁻}
            → s ≼ᵗ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
            ----------------------------
            → s ≼ᵗ[ k ] delay e t⁻

  -- spend slack to meet a demanded delay
  use-delay : ∀ {k d s⁻ t}
            → ∣ d ∣⁺ ≤ k
            → inj⁻ s⁻ ≼ᵗ[ k ∸ ∣ d ∣⁺ ] t
            ----------------------------
            → delay d s⁻ ≼ᵗ[ k ] t

-- the order proper grants no slack to begin with

infix 4 _≼ᵗ_

_≼ᵗ_ : Trace → Trace → Set
s ≼ᵗ t = s ≼ᵗ[ 0 ] t

-- rewriting the slack along an equation

coe : ∀ {j k s t} → j ≡ k → s ≼ᵗ[ j ] t → s ≼ᵗ[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any slack)
--
-- Unchanged from the lenient order except that the operation case now
-- recurses at slack zero, which is where the induction already was.

mutual

  ≼ᵗ-refl : ∀ {k} (s : Trace) → s ≼ᵗ[ k ] s
  ≼ᵗ-refl ε                = nil
  ≼ᵗ-refl (operation o s)  = keep (≼ᵗ-refl s)
  ≼ᵗ-refl {k} (delay d s⁻) =
    del-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼ᵗ-refl⁻ s⁻))

  ≼ᵗ-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼ᵗ[ k ] inj⁻ s⁻
  ≼ᵗ-refl⁻ ε⁻               = nil
  ≼ᵗ-refl⁻ (operation⁻ o s) = keep (≼ᵗ-refl s)

------------------------------------------------------------------------
-- Weakening: more slack is always fine
--
-- The `keep` case is now immediate: its premise does not mention the
-- slack being weakened.

weaken : ∀ {j s t} (m : ℕ) → s ≼ᵗ[ j ] t → s ≼ᵗ[ j + m ] t
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

del-op : ∀ {k o s t} → s ≼ᵗ[ k ] t → s ≼ᵗ[ k ] operation o t
del-op {k} {o} d = pay-op (weaken (cost o) d)

------------------------------------------------------------------------
-- Transitivity: the slacks add up
--
-- The only case that differs from the lenient order is `pay-op` against
-- `keep`: there the middle run's matched operation resets the slack, so
-- the inductive hypothesis lands at `(j + cost o) + 0` and has to be
-- weakened by `k` before it can be re-associated.

≼ᵗ-trans : ∀ {j k s t u} → s ≼ᵗ[ j ] t → t ≼ᵗ[ k ] u → s ≼ᵗ[ j + k ] u
≼ᵗ-trans nil _ = nil
-- the demand keeps an operation, which the middle run has: both sides
-- of the match are at slack zero, so the composite is too
≼ᵗ-trans (keep d1) (keep d2) = keep (≼ᵗ-trans d1 d2)
≼ᵗ-trans {j} {k} (keep d1) (pay-op {o = o} d2) =
  pay-op (coe (sym (+-assoc j k (cost o))) (≼ᵗ-trans {j} (keep d1) d2))
≼ᵗ-trans {j} {k} (keep d1) (del-delay {e = e} d2) =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᵗ-trans {j} (keep d1) d2))
-- the demand banks an operation of the middle run, which the run must
-- therefore also have; the match on the right resets the slack, so what
-- the hypothesis gives has to be weakened back up
≼ᵗ-trans {j} {k} (pay-op {o = o} d1) (keep d2) =
  pay-op (coe (lem-swap j (cost o) k)
              (weaken k (coe (+-identityʳ (j + cost o)) (≼ᵗ-trans d1 d2))))
≼ᵗ-trans {j} {k} (pay-op d1) (pay-op {o = o} d2) =
  pay-op (coe (sym (+-assoc j k (cost o))) (≼ᵗ-trans (pay-op d1) d2))
≼ᵗ-trans {j} {k} (pay-op d1) (del-delay {e = e} d2) =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺)) (≼ᵗ-trans (pay-op d1) d2))
-- the demand banks a delay of the middle run
≼ᵗ-trans {j} {k} (del-delay {e = e} d1) (use-delay p d2) =
  coe (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺)) (cong (j +_) (m+[n∸m]≡n p)))
      (≼ᵗ-trans d1 d2)
≼ᵗ-trans {j} {k} (del-delay d1) (pay-op {o = o} d2) =
  pay-op (coe (sym (+-assoc j k (cost o))) (≼ᵗ-trans (del-delay d1) d2))
≼ᵗ-trans {j} {k} (del-delay d1) (del-delay {e = f} d2) =
  del-delay (coe (sym (+-assoc j k ∣ f ∣⁺)) (≼ᵗ-trans (del-delay d1) d2))
-- the demand spends slack on its own leading delay
≼ᵗ-trans {j} {k} (use-delay {d = d} p d1) D2 =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼ᵗ-trans d1 D2))

------------------------------------------------------------------------
-- The time-strict order is a restriction of the lenient one
--
-- Every derivation here is one there: the only rule that changed asks
-- for *less* slack at the recursive call, which the lenient order's own
-- weakening supplies.

≼ᵗ→≼ : ∀ {j s t} → s ≼ᵗ[ j ] t → s ≼ˢ[ j ] t
≼ᵗ→≼ nil = nilˢ
≼ᵗ→≼ {j} (keep d) =
  keepˢ (coeˢ (trans (+-comm 0 j) (+-identityʳ j)) (weakenˢ j (≼ᵗ→≼ d)))
≼ᵗ→≼ (pay-op d)      = pay-opˢ (≼ᵗ→≼ d)
≼ᵗ→≼ (del-delay d)   = del-delayˢ (≼ᵗ→≼ d)
≼ᵗ→≼ (use-delay p d) = use-delayˢ p (≼ᵗ→≼ d)

------------------------------------------------------------------------
-- What the restriction buys
--
-- The demand `r · ⟨ 2 ⟩ · s` is met by a run that does an operation
-- *between* the read and the send, provided that operation takes at
-- least the two ticks demanded. This is the case the lenient order and
-- this one agree on; what they disagree about is a run doing that
-- operation before the read, which `Decidable` settles once it exists.

module Illustration (r w s : Op) (w-covers-2 : 2 ≤ cost w) where

  paid-in-between : (⌈ r ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ s ⌉) ≼ᵗ (⌈ r ⌉ ∙ ⌈ w ⌉ ∙ ⌈ s ⌉)
  paid-in-between = keep (pay-op (use-delay w-covers-2 (keep nil)))
