------------------------------------------------------------------------
-- Deciding the allowance relation.                                    --
--                                                                    --
-- By recursion on a fuel budget bounding the combined size of the two --
-- traces: every rule shrinks that size by at least one, and the       --
-- delay-free injection preserves it (`size-inj⁻`), so banking or      --
-- spending a leading delay counts as one step too.                    --
--                                                                    --
-- A leading delay of the *bound* settles the head on its own. Any     --
-- derivation against it moves that delay into the budget             --
-- (`bank-delay-inv`), so the case is one recursive call rather than a --
-- choice. Where the bound leads with an operation there is a real     --
-- choice -- skip it, or, if the run leads with an operation too,      --
-- match it or pay for it -- and matching recurses at budget zero,     --
-- where the rule puts its premise. Matching also needs decidable      --
-- equality of operation symbols, which is what `DecAllowance` takes   --
-- as a parameter.                                                     --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-monoʳ-≤; _≤?_; +-suc; n≤1+n)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ)

module Syntax.Grades.Traces.Allowance.Decidable (Op : Set) (costʰⁱ : Op → ℕ) where

open import Syntax.Grades.Traces.Base ℕᵀ Op

open import Syntax.Grades.Traces.Allowance.Core Op costʰⁱ
open import Syntax.Grades.Traces.Allowance.Moves Op costʰⁱ using (bank-delay-inv)

module DecAllowance (_≟ₒ_ : DecidableEquality Op) where

  dec : (n : ℕ) (s : Trace) (k : ℕ) (t : Trace)
      → size s + size t ≤ n → Dec (s ≼ᵃ[ k ] t)

  -- the empty run is permitted by every bound
  dec n ε k t le = yes nil

  -- an operation of the run against a spent bound
  dec (suc n) (operation o s') k ε (s≤s le)
    with costʰⁱ o ≤? k
  ... | no ¬p = no (λ { (use-op p _) → ¬p p })
  ... | yes p
          with dec n s' (k ∸ costʰⁱ o) ε le
  ...     | yes d  = yes (use-op p d)
  ...     | no ¬d = no (λ { (use-op _ d) → ¬d d })

  -- an operation of the run against one of the bound: skip, pay, or
  -- match -- and matching carries no budget across
  dec (suc n) (operation o s') k (operation o' t') (s≤s le)
    with dec n (operation o s') k t'
               (subst (_≤ n) (+-suc (size s') (size t')) le)
  ... | yes d = yes (skip-op d)
  ... | no ¬d
          with costʰⁱ o ≤? k
  ...     | yes p
              with dec n s' (k ∸ costʰⁱ o) (operation o' t') le
  ...         | yes d' = yes (use-op p d')
  ...         | no ¬d' with o ≟ₒ o'
  ...           | no ¬eq = no (λ { (keep _)      → ¬eq refl
                                 ; (skip-op d)   → ¬d d
                                 ; (use-op _ d') → ¬d' d' })
  ...           | yes refl
                    with dec n s' 0 t'
                             (≤-trans (+-monoʳ-≤ (size s') (n≤1+n (size t'))) le)
  ...               | yes d'' = yes (keep d'')
  ...               | no ¬d'' = no (λ { (keep d'')    → ¬d'' d''
                                      ; (skip-op d)   → ¬d d
                                      ; (use-op _ d') → ¬d' d' })
  dec (suc n) (operation o s') k (operation o' t') (s≤s le)
      | no ¬d | no ¬p with o ≟ₒ o'
  ...   | no ¬eq = no (λ { (keep _)     → ¬eq refl
                         ; (skip-op d)  → ¬d d
                         ; (use-op p _) → ¬p p })
  ...   | yes refl
            with dec n s' 0 t'
                     (≤-trans (+-monoʳ-≤ (size s') (n≤1+n (size t'))) le)
  ...       | yes d'' = yes (keep d'')
  ...       | no ¬d'' = no (λ { (keep d'')   → ¬d'' d''
                              ; (skip-op d)  → ¬d d
                              ; (use-op p _) → ¬p p })

  -- a leading delay of the bound: banked, and that settles it
  dec (suc n) (operation o s') k (delay e t⁻) (s≤s le)
    with dec n (operation o s') (k + ∣ e ∣⁺) (inj⁻ t⁻)
               (subst (λ z → suc (size s') + z ≤ n) (sym (size-inj⁻ t⁻))
                      (subst (_≤ n) (+-suc (size s') (size⁻ t⁻)) le))
  ... | yes d  = yes (bank-delay d)
  ... | no ¬d = no (λ deriv → ¬d (bank-delay-inv deriv))

  -- a delay of the run against a spent bound
  dec (suc n) (delay d s⁻) k ε (s≤s le)
    with ∣ d ∣⁺ ≤? k
  ... | no ¬p = no (λ { (use-delay p _) → ¬p p })
  ... | yes p
          with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) ε
                   (subst (λ z → z + size ε ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...     | yes d'  = yes (use-delay p d')
  ...     | no ¬d' = no (λ { (use-delay _ d') → ¬d' d' })

  -- a delay of the run against an operation of the bound
  dec (suc n) (delay d s⁻) k (operation o' t') (s≤s le)
    with dec n (delay d s⁻) k t'
               (subst (_≤ n) (+-suc (size⁻ s⁻) (size t')) le)
  ... | yes d'' = yes (skip-op d'')
  ... | no ¬d'' with ∣ d ∣⁺ ≤? k
  ...   | no ¬p = no (λ { (use-delay p _) → ¬p p
                        ; (skip-op d'')   → ¬d'' d'' })
  ...   | yes p
            with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) (operation o' t')
                     (subst (λ z → z + suc (size t') ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...       | yes d'  = yes (use-delay p d')
  ...       | no ¬d' = no (λ { (use-delay _ d') → ¬d' d'
                             ; (skip-op d'')    → ¬d'' d'' })

  -- a delay of the run against one of the bound
  dec (suc n) (delay d s⁻) k (delay e t⁻) (s≤s le)
    with dec n (delay d s⁻) (k + ∣ e ∣⁺) (inj⁻ t⁻)
               (subst (λ z → suc (size⁻ s⁻) + z ≤ n) (sym (size-inj⁻ t⁻))
                      (subst (_≤ n) (+-suc (size⁻ s⁻) (size⁻ t⁻)) le))
  ... | yes d'' = yes (bank-delay d'')
  ... | no ¬d'' = no (λ deriv → ¬d'' (bank-delay-inv deriv))

  -- the decision procedure at a given budget

  infix 4 _≼ᵃ[_]?_

  _≼ᵃ[_]?_ : (s : Trace) (k : ℕ) (t : Trace) → Dec (s ≼ᵃ[ k ] t)
  s ≼ᵃ[ k ]? t = dec (size s + size t) s k t ≤-refl

  -- the time-strict allowance order proper (no budget)

  infix 4 _≼ᵃ?_

  _≼ᵃ?_ : (s t : Trace) → Dec (s ≼ᵃ t)
  s ≼ᵃ? t = s ≼ᵃ[ 0 ]? t
