------------------------------------------------------------------------
-- Deciding the coverage relation.                                     --
--                                                                     --
-- A backtracking search on the two heads, driven by fuel: every        --
-- constructor shrinks the combined size of the two traces by at least  --
-- one, so the combined size is fuel enough. Matching an operation      --
-- recurses at slack *zero*, which is where `keep` puts its premise --   --
-- the banked slack is simply dropped at the match.                     --
--                                                                     --
-- The size measure is shared with the allowance order: it speaks only  --
-- about traces, not about either relation.                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-monoʳ-≤; _≤?_; +-suc; n≤1+n)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

module Syntax.Grades.Traces.Coverage.Decidable (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺)


open import Syntax.Grades.Traces.Coverage.Core Op cost

module DecCoverage (_≟ₒ_ : DecidableEquality Op) where

  dec : (n : ℕ) (s : Trace) (k : ℕ) (t : Trace)
      → size s + size t ≤ n → Dec (s ≼ᶜ[ k ] t)

  -- the empty demand is met by any run
  dec n ε k t le = yes nil

  -- a demanded operation and a spent run: no rule applies, which is the
  -- whole point of the order -- time never buys an operation
  dec (suc n) (operation o s') k ε (s≤s le) = no λ ()

  -- a demanded operation against an operation of the run: bank the
  -- run's operation, or match it once the two symbols agree
  dec (suc n) (operation o s') k (operation o' t') (s≤s le)
    with dec n (operation o s') (k + cost o') t'
                (subst (_≤ n) (+-suc (size s') (size t')) le)
  ... | yes d = yes (pay-op d)
  ... | no ¬d with o ≟ₒ o'
  ...   | no ¬eq = no (λ { (keep _)  → ¬eq refl
                         ; (pay-op d) → ¬d d })
  ...   | yes refl
            with dec n s' 0 t'
                     (≤-trans (+-monoʳ-≤ (size s') (n≤1+n (size t'))) le)
  ...       | yes d' = yes (keep d')
  ...       | no ¬d' = no (λ { (keep d')  → ¬d' d'
                             ; (pay-op d) → ¬d d })

  -- a demanded operation against a delay of the run: the delay is
  -- banked, and nothing else can happen
  dec (suc n) (operation o s') k (delay e t⁻) (s≤s le)
    with dec n (operation o s') (k + ∣ e ∣⁺) (inj⁻ t⁻)
               (subst (λ z → suc (size s') + z ≤ n) (sym (size-inj⁻ t⁻))
                      (subst (_≤ n) (+-suc (size s') (size⁻ t⁻)) le))
  ... | yes d  = yes (del-delay d)
  ... | no ¬d = no (λ { (del-delay d) → ¬d d })

  -- a demanded delay and a spent run: pay it out of the slack
  dec (suc n) (delay d s⁻) k ε (s≤s le)
    with ∣ d ∣⁺ ≤? k
  ... | no ¬p = no (λ { (use-delay p _) → ¬p p })
  ... | yes p
          with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) ε
                   (subst (λ z → z + size ε ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...     | yes d'  = yes (use-delay p d')
  ...     | no ¬d' = no (λ { (use-delay _ d') → ¬d' d' })

  -- a demanded delay against an operation of the run: pay the delay out
  -- of the slack, or bank the operation into it
  dec (suc n) (delay d s⁻) k (operation o' t') (s≤s le)
    with dec n (delay d s⁻) (k + cost o') t'
               (subst (_≤ n) (+-suc (size⁻ s⁻) (size t')) le)
  ... | yes d'' = yes (pay-op d'')
  ... | no ¬d'' with ∣ d ∣⁺ ≤? k
  ...   | no ¬p = no (λ { (use-delay p _) → ¬p p
                        ; (pay-op d'')    → ¬d'' d'' })
  ...   | yes p
            with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) (operation o' t')
                     (subst (λ z → z + suc (size t') ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...       | yes d'  = yes (use-delay p d')
  ...       | no ¬d' = no (λ { (use-delay _ d') → ¬d' d'
                             ; (pay-op d'')     → ¬d'' d'' })

  -- a demanded delay against a delay of the run: pay or bank
  dec (suc n) (delay d s⁻) k (delay e t⁻) (s≤s le)
    with dec n (delay d s⁻) (k + ∣ e ∣⁺) (inj⁻ t⁻)
               (subst (λ z → suc (size⁻ s⁻) + z ≤ n) (sym (size-inj⁻ t⁻))
                      (subst (_≤ n) (+-suc (size⁻ s⁻) (size⁻ t⁻)) le))
  ... | yes d'' = yes (del-delay d'')
  ... | no ¬d'' with ∣ d ∣⁺ ≤? k
  ...   | no ¬p = no (λ { (use-delay p _) → ¬p p
                        ; (del-delay d'') → ¬d'' d'' })
  ...   | yes p
            with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) (delay e t⁻)
                     (subst (λ z → z + suc (size⁻ t⁻) ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...       | yes d'  = yes (use-delay p d')
  ...       | no ¬d' = no (λ { (use-delay _ d') → ¬d' d'
                             ; (del-delay d'')  → ¬d'' d'' })

  -- the decision procedure at a given slack

  infix 4 _≼ᶜ[_]?_

  _≼ᶜ[_]?_ : (s : Trace) (k : ℕ) (t : Trace) → Dec (s ≼ᶜ[ k ] t)
  s ≼ᶜ[ k ]? t = dec (size s + size t) s k t ≤-refl

  -- the coverage order proper (no slack)

  infix 4 _≼ᶜ?_

  _≼ᶜ?_ : (s t : Trace) → Dec (s ≼ᶜ t)
  s ≼ᶜ? t = s ≼ᶜ[ 0 ]? t
