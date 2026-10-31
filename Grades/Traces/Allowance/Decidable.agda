-------------------------------------------------------------------------
-- Deciding the allowance relation.                                    --
--                                                                     --
-- By recursion on a fuel budget bounding the combined size of the two --
-- traces: every rule shrinks that size by at least one, and the       --
-- delay-free injection preserves it (`size-inj⁻`), so banking or      --
-- spending a leading delay counts as one step too.                    --
--                                                                     --
-- A leading delay of the bound settles the head on its own: any       --
-- derivation against it moves that delay into the budget              --
-- (`bank-delay-inv`), so the case is one recursive call, not a        --
-- choice. Where the bound leads with an operation there is a choice:  --
-- skip it, or, if the run leads with an operation too, match it or    --
-- pay for it; matching recurses at budget zero, where the rule puts   --
-- its premise, and needs decidable equality of operation symbols,     --
-- the parameter of `DecAllowance`.                                    --
-------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; s≤s)
open import Data.Nat.Properties using (+-suc; n≤1+n)
import Data.Nat.Base as ℕ
import Data.Nat.Properties as ℕ

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Allowance.Decidable
  {D : Duration} (T : TimeDomain D) (Op : Set) (costʰⁱ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Base T Op

open import Grades.Traces.Allowance.Core T Op costʰⁱ
open import Grades.Traces.Allowance.Moves T Op costʰⁱ using (bank-delay-inv)

module DecAllowance (_≟ₒ_ : DecidableEquality Op) where

  dec : (n : ℕ) (s : Trace) (k : Carrier) (t : Trace)
      → size s ℕ.+ size t ℕ.≤ n → Dec (s ≼ᵃ[ k ] t)

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
  -- match, carrying no budget across
  dec (suc n) (operation o s') k (operation o' t') (s≤s le)
    with dec n (operation o s') k t'
               (subst (ℕ._≤ n) (+-suc (size s') (size t')) le)
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
                    with dec n s' 0ᴰ t'
                             (ℕ.≤-trans (ℕ.+-monoʳ-≤ (size s') (n≤1+n (size t'))) le)
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
            with dec n s' 0ᴰ t'
                     (ℕ.≤-trans (ℕ.+-monoʳ-≤ (size s') (n≤1+n (size t'))) le)
  ...       | yes d'' = yes (keep d'')
  ...       | no ¬d'' = no (λ { (keep d'')   → ¬d'' d''
                              ; (skip-op d)  → ¬d d
                              ; (use-op p _) → ¬p p })

  -- a leading delay of the bound: banked, and that settles it
  dec (suc n) (operation o s') k (delay e t⁻) (s≤s le)
    with dec n (operation o s') (k + ∣ e ∣⁺) (inj⁻ t⁻)
               (subst (λ z → suc (size s') ℕ.+ z ℕ.≤ n) (sym (size-inj⁻ t⁻))
                      (subst (ℕ._≤ n) (+-suc (size s') (size⁻ t⁻)) le))
  ... | yes d  = yes (bank-delay d)
  ... | no ¬d = no (λ deriv → ¬d (bank-delay-inv deriv))

  -- a delay of the run against a spent bound
  dec (suc n) (delay d s⁻) k ε (s≤s le)
    with ∣ d ∣⁺ ≤? k
  ... | no ¬p = no (λ { (use-delay p _) → ¬p p })
  ... | yes p
          with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) ε
                   (subst (λ z → z ℕ.+ size ε ℕ.≤ n) (sym (size-inj⁻ s⁻)) le)
  ...     | yes d'  = yes (use-delay p d')
  ...     | no ¬d' = no (λ { (use-delay _ d') → ¬d' d' })

  -- a delay of the run against an operation of the bound
  dec (suc n) (delay d s⁻) k (operation o' t') (s≤s le)
    with dec n (delay d s⁻) k t'
               (subst (ℕ._≤ n) (+-suc (size⁻ s⁻) (size t')) le)
  ... | yes d'' = yes (skip-op d'')
  ... | no ¬d'' with ∣ d ∣⁺ ≤? k
  ...   | no ¬p = no (λ { (use-delay p _) → ¬p p
                        ; (skip-op d'')   → ¬d'' d'' })
  ...   | yes p
            with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) (operation o' t')
                     (subst (λ z → z ℕ.+ suc (size t') ℕ.≤ n) (sym (size-inj⁻ s⁻)) le)
  ...       | yes d'  = yes (use-delay p d')
  ...       | no ¬d' = no (λ { (use-delay _ d') → ¬d' d'
                             ; (skip-op d'')    → ¬d'' d'' })

  -- a delay of the run against one of the bound
  dec (suc n) (delay d s⁻) k (delay e t⁻) (s≤s le)
    with dec n (delay d s⁻) (k + ∣ e ∣⁺) (inj⁻ t⁻)
               (subst (λ z → suc (size⁻ s⁻) ℕ.+ z ℕ.≤ n) (sym (size-inj⁻ t⁻))
                      (subst (ℕ._≤ n) (+-suc (size⁻ s⁻) (size⁻ t⁻)) le))
  ... | yes d'' = yes (bank-delay d'')
  ... | no ¬d'' = no (λ deriv → ¬d'' (bank-delay-inv deriv))

  -- the decision procedure at a given budget

  infix 4 _≼ᵃ[_]?_

  _≼ᵃ[_]?_ : (s : Trace) (k : Carrier) (t : Trace) → Dec (s ≼ᵃ[ k ] t)
  s ≼ᵃ[ k ]? t = dec (size s ℕ.+ size t) s k t ℕ.≤-refl

  -- the time-strict allowance order proper (no budget)

  infix 4 _≼ᵃ?_

  _≼ᵃ?_ : (s t : Trace) → Dec (s ≼ᵃ t)
  s ≼ᵃ? t = s ≼ᵃ[ 0ᴰ ]? t
