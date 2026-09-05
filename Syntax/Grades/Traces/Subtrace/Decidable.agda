------------------------------------------------------------------------
-- Deciding the sub-trace relation.                                    --
--                                                                     --
-- The relation is decided by recursion on a fuel budget bounding the   --
-- combined size of the two traces. Every constructor shrinks that      --
-- combined size by at least one, so the budget always suffices; the    --
-- delay-free injection preserves size (`size-inj⁻`), so absorbing or   --
-- spending a leading delay counts as one step too.                     --
--                                                                     --
-- Keeping a leading operation requires deciding equality of the two    --
-- operation symbols, so everything here sits inside `DecSubtrace`,     --
-- which takes that decision as a parameter.                            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-monoʳ-≤; _≤?_; +-suc; n≤1+n)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no)

open import Util.Equality

module Syntax.Grades.Traces.Subtrace.Decidable (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺)

open import Syntax.Grades.Traces.Subtrace.Core Op cost

module DecSubtrace (_≟ₒ_ : DecidableEquality Op) where

  dec : (n : ℕ) (s : Trace) (k : ℕ) (t : Trace)
      → size s + size t ≤ n → Dec (s ≼[ k ] t)

  -- Deciding whether the leading operation of the left-hand trace can be
  -- paid for out of the slack. Each of the three clauses with an operation
  -- on the left consults this once, so the alternatives left to them are
  -- fixed by the shape of the right-hand trace alone.

  dec-use-op : (n : ℕ) (o : Op) (s' : Trace) (k : ℕ) (t : Trace)
             → size s' + size t ≤ n
             → Dec ((cost o ≤ k) × (s' ≼[ k ∸ cost o ] t))

  dec-use-op n o s' k t le
    with cost o ≤? k
  ... | no ¬p = no (λ { (p , _) → ¬p p })
  ... | yes p
          with dec n s' (k ∸ cost o) t le
  ...     | yes d  = yes (p , d)
  ...     | no ¬d = no (λ { (_ , d) → ¬d d })

  -- the empty trace lies below anything
  dec n ε k t le = yes nil

  -- a leading operation on the left, nothing on the right: the operation
  -- has to be paid for out of the slack
  dec (suc n) (operation o s') k ε (s≤s le)
    with dec-use-op n o s' k ε le
  ... | yes (p , d) = yes (use-op p d)
  ... | no ¬u      = no (λ { (use-op p d) → ¬u (p , d) })

  -- a leading operation on both sides: pay for it out of the slack
  -- (`use-op`), delete it on the right (`del-op`), or keep it (`keep`,
  -- once the two operation symbols agree)
  dec (suc n) (operation o s') k (operation o' t') (s≤s le)
    with dec-use-op n o s' k (operation o' t') le
  ... | yes (p , d) = yes (use-op p d)
  ... | no ¬u
          with dec n (operation o s') k t'
                      (subst (_≤ n) (+-suc (size s') (size t')) le)
  ...     | yes d = yes (del-op d)
  ...     | no ¬d with o ≟ₒ o'
  ...       | no ¬eq = no (λ { (keep _)      → ¬eq refl
                            ; (use-op p d)  → ¬u (p , d)
                            ; (del-op d)    → ¬d d })
  ...       | yes refl
                with dec n s' k t'
                         (≤-trans (+-monoʳ-≤ (size s') (n≤1+n (size t'))) le)
  ...         | yes d'  = yes (keep d')
  ...         | no ¬d' = no (λ { (keep d')     → ¬d' d'
                              ; (use-op p d)  → ¬u (p , d)
                              ; (del-op d)    → ¬d d })

  -- a leading operation on the left, a leading delay on the right: pay
  -- for the operation out of the slack (`use-op`) or absorb the delay
  -- into the slack (`del-delay`)
  dec (suc n) (operation o s') k (delay e t⁻) (s≤s le)
    with dec-use-op n o s' k (delay e t⁻) le
  ... | yes (p , d) = yes (use-op p d)
  ... | no ¬u
          with dec n (operation o s') (k + ∣ e ∣⁺) (inj⁻ t⁻)
                      (subst (λ z → suc (size s') + z ≤ n) (sym (size-inj⁻ t⁻))
                             (subst (_≤ n) (+-suc (size s') (size⁻ t⁻)) le))
  ...     | yes d  = yes (del-delay d)
  ...     | no ¬d = no (λ { (del-delay d) → ¬d d
                          ; (use-op p d)  → ¬u (p , d) })

  -- a leading delay on the left, nothing on the right: spend slack on it
  dec (suc n) (delay d s⁻) k ε (s≤s le)
    with ∣ d ∣⁺ ≤? k
  ... | no ¬p = no (λ { (use-delay p _) → ¬p p })
  ... | yes p
          with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) ε
                   (subst (λ z → z + size ε ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...     | yes d'  = yes (use-delay p d')
  ...     | no ¬d' = no (λ { (use-delay _ d') → ¬d' d' })

  -- a leading delay on the left, a leading operation on the right:
  -- spend slack on the delay (`use-delay`) or delete the operation
  -- on the right (`del-op`)
  dec (suc n) (delay d s⁻) k (operation o' t') (s≤s le)
    with ∣ d ∣⁺ ≤? k
  ... | yes p
          with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) (operation o' t')
                   (subst (λ z → z + suc (size t') ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...     | yes d'  = yes (use-delay p d')
  ...     | no ¬u
              with dec n (delay d s⁻) k t'
                       (subst (_≤ n) (+-suc (size⁻ s⁻) (size t')) le)
  ...         | yes d'' = yes (del-op d'')
  ...         | no ¬d'' = no (λ { (use-delay _ d') → ¬u d'
                               ; (del-op d'')     → ¬d'' d'' })
  dec (suc n) (delay d s⁻) k (operation o' t') (s≤s le)
    | no ¬p
        with dec n (delay d s⁻) k t'
                 (subst (_≤ n) (+-suc (size⁻ s⁻) (size t')) le)
  ...   | yes d'' = yes (del-op d'')
  ...   | no ¬d'' = no (λ { (use-delay p _) → ¬p p
                         ; (del-op d'')    → ¬d'' d'' })

  -- a leading delay on both sides: spend slack on the left delay
  -- (`use-delay`) or absorb the right delay into the slack (`del-delay`)
  dec (suc n) (delay d s⁻) k (delay e t⁻) (s≤s le)
    with ∣ d ∣⁺ ≤? k
  ... | yes p
          with dec n (inj⁻ s⁻) (k ∸ ∣ d ∣⁺) (delay e t⁻)
                   (subst (λ z → z + suc (size⁻ t⁻) ≤ n) (sym (size-inj⁻ s⁻)) le)
  ...     | yes d'  = yes (use-delay p d')
  ...     | no ¬u
              with dec n (delay d s⁻) (k + ∣ e ∣⁺) (inj⁻ t⁻)
                       (subst (λ z → suc (size⁻ s⁻) + z ≤ n) (sym (size-inj⁻ t⁻))
                              (subst (_≤ n) (+-suc (size⁻ s⁻) (size⁻ t⁻)) le))
  ...         | yes d'' = yes (del-delay d'')
  ...         | no ¬d'' = no (λ { (use-delay _ d') → ¬u d'
                               ; (del-delay d'')  → ¬d'' d'' })
  dec (suc n) (delay d s⁻) k (delay e t⁻) (s≤s le)
    | no ¬p
        with dec n (delay d s⁻) (k + ∣ e ∣⁺) (inj⁻ t⁻)
                 (subst (λ z → suc (size⁻ s⁻) + z ≤ n) (sym (size-inj⁻ t⁻))
                        (subst (_≤ n) (+-suc (size⁻ s⁻) (size⁻ t⁻)) le))
  ...   | yes d'' = yes (del-delay d'')
  ...   | no ¬d'' = no (λ { (use-delay p _) → ¬p p
                         ; (del-delay d'')  → ¬d'' d'' })

  -- the decision procedure at a given slack

  infix 4 _≼[_]?_

  _≼[_]?_ : (s : Trace) (k : ℕ) (t : Trace) → Dec (s ≼[ k ] t)
  s ≼[ k ]? t = dec (size s + size t) s k t ≤-refl

  -- the sub-trace order proper (no slack)

  infix 4 _≼?_

  _≼?_ : (s t : Trace) → Dec (s ≼ t)
  s ≼? t = s ≼[ 0 ]? t
