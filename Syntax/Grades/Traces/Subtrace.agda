------------------------------------------------------------------------
-- A sub-trace preorder on timed traces, relative to a cost on         --
-- operation symbols                                                    --
--                                                                    --
-- Operations come with a prescribed execution time: performing `o`     --
-- takes `cost o` units. A leading operation of the *left-hand* trace   --
-- may therefore be paid for out of the slack, at its execution time,   --
-- exactly as a leading delay is (`use-op` alongside `use-delay`). An   --
-- operation performed thus fits inside a pure time budget on the       --
-- right, `⌈ o ⌉ ≼ ⟨ n ⟩` as soon as `cost o ≤ n`.                     --
--                                                                    --
-- The converse never holds: slack is created only by absorbing the     --
-- *delays* of the right-hand trace (`del-delay`), and deleting one of  --
-- its operations (`del-op`) frees none. A right-hand trace that calls  --
-- for an operation is therefore not met by spending the same amount of --
-- time on anything else.                                              --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-comm; +-assoc; ≤-refl; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+n∸n≡m; m+[n∸m]≡n; m∸n+n≡m; +-monoʳ-≤; ∸-+-assoc; +-∸-assoc;
         _≤?_; +-suc; n≤1+n)
open import Data.Product using (_×_; _,_)

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Util.Equality

-- Sub-trace orders are parameterised by a set `Op` of operation names
-- and by the map `cost` giving each operation its execution time.

module Syntax.Grades.Traces.Subtrace (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺; ∣1+∣⁺)

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
-- decision procedure below: every recursive call strictly decreases it.

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
-- The slack-indexed sub-trace relation

infix 4 _≼[_]_

data _≼[_]_ : Trace → ℕ → Trace → Set where

  -- the empty trace lies below anything: drop all operations of `t` and
  -- decrease all of its delays to zero
  nil       : ∀ {k t} 
            ------------
            → ε ≼[ k ] t

  -- keep a leading operation (no leading delay on either side)
  keep      : ∀ {k o s t} 
            → s ≼[ k ] t 
            ------------------------------------
            → operation o s ≼[ k ] operation o t

  -- delete the leading operation of the right-hand trace
  del-op    : ∀ {k o s t} 
            → s ≼[ k ] t 
            ------------------------
            → s ≼[ k ] operation o t

  -- absorb the leading delay of the right-hand trace into the slack;
  -- this is what lets several right-hand delays collapse together as the
  -- operations between them are deleted
  del-delay : ∀ {k e s t⁻} 
            → s ≼[ k + ∣ e ∣⁺ ] inj⁻ t⁻ 
            ---------------------------
            → s ≼[ k ] delay e t⁻

  -- spend slack to cover the leading operation of the left-hand trace,
  -- at the execution time that operation takes
  use-op    : ∀ {k o s t}
            → cost o ≤ k
            → s ≼[ k ∸ cost o ] t
            ------------------------
            → operation o s ≼[ k ] t

  -- spend slack to cover the leading delay of the left-hand trace
  use-delay : ∀ {k d s⁻ t}
            → ∣ d ∣⁺ ≤ k
            → inj⁻ s⁻ ≼[ k ∸ ∣ d ∣⁺ ] t
            ---------------------------
            → delay d s⁻ ≼[ k ] t

-- the sub-trace order proper grants no extra slack

infix 4 _≼_

_≼_ : Trace → Trace → Set
s ≼ t = s ≼[ 0 ] t

-- rewriting the slack along an equation (the endpoints are fixed, so
-- this is just transport and avoids leaving them as metavariables)

coe : ∀ {j k s t} → j ≡ k → s ≼[ j ] t → s ≼[ k ] t
coe refl p = p

------------------------------------------------------------------------
-- Reflexivity (at any slack)

mutual

  ≼-refl : ∀ {k} (s : Trace) → s ≼[ k ] s
  ≼-refl ε                 = nil
  ≼-refl (operation o s)   = keep (≼-refl s)
  ≼-refl {k} (delay d s⁻)  =
    del-delay (use-delay (m≤n+m ∣ d ∣⁺ k) (≼-refl⁻ s⁻))

  ≼-refl⁻ : ∀ {k} (s⁻ : Trace⁻) → inj⁻ s⁻ ≼[ k ] inj⁻ s⁻
  ≼-refl⁻ ε⁻               = nil
  ≼-refl⁻ (operation⁻ o s) = keep (≼-refl s)

------------------------------------------------------------------------
-- Weakening: more slack is always fine

weaken : ∀ {j s t} (m : ℕ) → s ≼[ j ] t → s ≼[ j + m ] t
weaken m nil                       = nil
weaken m (keep d)                  = keep (weaken m d)
weaken m (del-op d)                = del-op (weaken m d)
weaken {j} m (del-delay {e = e} d) =
  del-delay (coe (lem-swap j ∣ e ∣⁺ m) (weaken m d))
weaken {j} m (use-op p d') =
  use-op (≤-trans p (m≤m+n j m))
         (coe (sym (+-∸-comm m p)) (weaken m d'))
weaken {j} m (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n j m))
            (coe (sym (+-∸-comm m p)) (weaken m d'))

------------------------------------------------------------------------
-- Transitivity: the slacks add up

≼-trans : ∀ {j k s t u} → s ≼[ j ] t → t ≼[ k ] u → s ≼[ j + k ] u
≼-trans nil                       _                       = nil
-- left factor keeps an operation
≼-trans (keep d1)        (keep d2)                        = keep (≼-trans d1 d2)
≼-trans {j} {k} (keep d1) (use-op p d2)                   =
  use-op (≤-trans p (m≤n+m k j))
         (coe (sym (+-∸-assoc j p)) (≼-trans d1 d2))
≼-trans (keep d1)        (del-op d2)                      = del-op (≼-trans (keep d1) d2)
≼-trans {j} {k} (keep d1) (del-delay {e = e} d2)          =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺))
            (≼-trans (keep d1) d2))
-- left factor deletes an operation of the middle trace
≼-trans (del-op d1)      (keep d2)                        = del-op (≼-trans d1 d2)
≼-trans {j} {k} (del-op d1) (use-op {o = o} p d2)         =
  coe (trans (+-assoc j (k ∸ cost o) (cost o))
             (cong (j +_) (m∸n+n≡m p)))
      (weaken (cost o) (≼-trans d1 d2))
≼-trans (del-op d1)      (del-op d2)                      = del-op (≼-trans (del-op d1) d2)
≼-trans {j} {k} (del-op d1) (del-delay {e = e} d2)        =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺))
            (≼-trans (del-op d1) d2))
-- left factor absorbs the leading delay of the middle trace
≼-trans {j} {k} (del-delay {e = e} d1) (use-delay p d2)   =
  coe
        (trans (+-assoc j ∣ e ∣⁺ (k ∸ ∣ e ∣⁺)) (cong (j +_) (m+[n∸m]≡n p)))
        (≼-trans d1 d2)
≼-trans (del-delay d1)   (del-op d2)                      = del-op (≼-trans (del-delay d1) d2)
≼-trans {j} {k} (del-delay d1) (del-delay {e = f} d2)     =
  del-delay (coe (sym (+-assoc j k ∣ f ∣⁺))
            (≼-trans (del-delay d1) d2))
-- left factor spends slack on its own leading operation or delay
≼-trans {j} {k} (use-op p d1) D2                          =
  use-op (≤-trans p (m≤m+n j k))
         (coe (sym (+-∸-comm k p)) (≼-trans d1 D2))
≼-trans {j} {k} (use-delay {d = d} p d1) D2               =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼-trans d1 D2))

------------------------------------------------------------------------
-- Operations do not pay for delays
--
-- Slack is created by `del-delay` alone, so a right-hand trace built
-- from operations offers none, however long those operations take, and
-- the leading delay of `⟨ suc n ⟩` cannot be covered. Time spent on
-- operations therefore never stands in for a schedule's delay -- the
-- converse of `use-op` letting an operation be covered by a delay.

data Delay-free : Trace → Set where
  ε-free  : Delay-free ε
  op-free : ∀ {o t} → Delay-free t → Delay-free (operation o t)

1+≰0 : (n : ℕ) → ¬ (∣ 1+ n ∣⁺ ≤ zero)
1+≰0 n p with subst (_≤ zero) (∣1+∣⁺ n) p
... | ()

⟨suc⟩-⋠ : (n : ℕ) {t : Trace} → Delay-free t → ¬ (⟨ suc n ⟩ ≼ t)
⟨suc⟩-⋠ n ε-free      (use-delay p _) = 1+≰0 n p
⟨suc⟩-⋠ n (op-free _) (use-delay p _) = 1+≰0 n p
⟨suc⟩-⋠ n (op-free f) (del-op d)      = ⟨suc⟩-⋠ n f d

------------------------------------------------------------------------
-- Inversion of `del-delay`: a leading delay on the right can always be
-- moved back into the slack

del-delay-inv : ∀ {k e t t⁻} → t ≼[ k ] delay e t⁻ → t ≼[ k + ∣ e ∣⁺ ] inj⁻ t⁻
del-delay-inv nil               = nil
del-delay-inv (del-delay d)     = d
del-delay-inv {k} {e} (use-op p d') =
  use-op (≤-trans p (m≤m+n k ∣ e ∣⁺))
         (coe (sym (+-∸-comm ∣ e ∣⁺ p)) (del-delay-inv d'))
del-delay-inv {k} {e} (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n k ∣ e ∣⁺))
            (coe (sym (+-∸-comm ∣ e ∣⁺ p)) (del-delay-inv d'))

------------------------------------------------------------------------
-- Prepending a delay to the right-hand trace, modulo slack
--
-- `prepend d t'` adds a leading delay `d` to `t'`, so a trace lies below
-- it with `∣ d ∣⁺` units less slack.

absorbR : ∀ {k t} (d : ℕ⁺) (t' : Trace)
        → t ≼[ k + ∣ d ∣⁺ ] t' → t ≼[ k ] prepend d t'
absorbR d ε                hyp = del-delay hyp
absorbR d (operation o t') hyp = del-delay hyp
absorbR {k} d (delay e t'⁻) hyp =
  del-delay
    (coe
           (trans (+-assoc k ∣ d ∣⁺ ∣ e ∣⁺) (cong (k +_) (sym (∣∣⁺-+⁺ d e))))
           (del-delay-inv hyp))

------------------------------------------------------------------------
-- Bumping a leading delay on the left, paid for by equal extra slack

bumpL : ∀ {m e Z⁻ Y} (d : ℕ⁺)
      → delay e Z⁻ ≼[ m ] Y → delay (d +⁺ e) Z⁻ ≼[ m + ∣ d ∣⁺ ] Y
bumpL {m} d (use-delay {d = e} p prem) =
  use-delay
    (subst (_≤ m + ∣ d ∣⁺) (sym (∣∣⁺-+⁺ d e)) (≤-bump ∣ d ∣⁺ ∣ e ∣⁺ m p))
    (coe
           (sym (trans (cong ((m + ∣ d ∣⁺) ∸_) (∣∣⁺-+⁺ d e))
                       (∸-cancel m ∣ d ∣⁺ ∣ e ∣⁺)))
           prem)
bumpL d (del-op prem)               = del-op (bumpL d prem)
bumpL {m} d (del-delay {e = f} prem) =
  del-delay (coe (lem-swap m ∣ f ∣⁺ ∣ d ∣⁺) (bumpL d prem))

------------------------------------------------------------------------
-- Spending slack on a leading delay of `prepend d X`

spendL : ∀ {c t} (d : ℕ⁺) (X : Trace) → ∣ d ∣⁺ ≤ c
       → X ≼[ c ∸ ∣ d ∣⁺ ] t → prepend d X ≼[ c ] t
spendL d ε                p hyp = use-delay p hyp
spendL d (operation o X') p hyp = use-delay p hyp
spendL {c} d (delay e X'⁻) p hyp =
  coe (m∸n+n≡m p) (bumpL d hyp)

------------------------------------------------------------------------
-- Prepending content to the right-hand trace

-- adding a leading delay preserves the relation (same slack)

pad-delay : ∀ {k t t'} (d : ℕ⁺) → t ≼[ k ] t' → t ≼[ k ] prepend d t'
pad-delay d D = absorbR d _ (weaken ∣ d ∣⁺ D)

-- prefixing any trace `c` on the right preserves the relation

pad-left : ∀ {k t t'} (c : Trace) → t ≼[ k ] t' → t ≼[ k ] (c ∙ t')
pad-left ε                          D = D
pad-left (operation o c')           D = del-op (pad-left c' D)
pad-left (delay d ε⁻)               D = pad-delay d D
pad-left {k} (delay d (operation⁻ o c'')) D =
  del-delay (del-op (weaken ∣ d ∣⁺ (pad-left c'' D)))

------------------------------------------------------------------------
-- A trace below ε prefixes harmlessly on the left of a product

prepend-left : ∀ {c sₐ} (t : Trace) → sₐ ≼[ c ] ε → (sₐ ∙ t) ≼[ c ] t
prepend-left t nil                                       = ≼-refl t
prepend-left t (use-op p d)                              =
  use-op p (prepend-left t d)
prepend-left {c} t (use-delay {d = d} {s⁻ = ε⁻} p _)     =
  spendL d t p (≼-refl t)
prepend-left t (use-delay {s⁻ = operation⁻ o s''} p d')  =
  use-delay p (prepend-left t d')

------------------------------------------------------------------------
-- Monotonicity of the trace product (the slacks add up)

mono-∙ : ∀ {j k s s' t t'}
       → s ≼[ j ] s' → t ≼[ k ] t' → (s ∙ t) ≼[ j + k ] (s' ∙ t')
mono-∙ {j} {k} {s' = s'} nil D2 =
  coe (+-comm k j) (weaken j (pad-left s' D2))
mono-∙ (keep d1)   D2 = keep   (mono-∙ d1 D2)
mono-∙ (del-op d1) D2 = del-op (mono-∙ d1 D2)
mono-∙ {j} {k} {t' = t'} (del-delay {e = e} {t⁻ = ε⁻} d1) D2 =
  absorbR e _
    (coe (lem-swap j ∣ e ∣⁺ k)
           (≼-trans (prepend-left _ d1) D2))
mono-∙ {j} {k} (del-delay {e = e} {t⁻ = operation⁻ o s'''} d1) D2 =
  del-delay (coe (lem-swap j ∣ e ∣⁺ k) (mono-∙ d1 D2))
mono-∙ {j} {k} (use-op p d1) D2 =
  use-op (≤-trans p (m≤m+n j k))
         (coe (sym (+-∸-comm k p)) (mono-∙ d1 D2))
mono-∙ {j} {k} {s' = s'} (use-delay {d = d} {s⁻ = ε⁻} p d1) D2 =
  spendL d _ (≤-trans p (m≤m+n j k))
    (coe
           (trans (+-comm k (j ∸ ∣ d ∣⁺)) (sym (+-∸-comm k p)))
           (weaken (j ∸ ∣ d ∣⁺) (pad-left s' D2)))
mono-∙ {j} {k} (use-delay {d = d} {s⁻ = operation⁻ o s''} p d1) D2 =
  use-delay (≤-trans p (m≤m+n j k))
    (coe (sym (+-∸-comm k p)) (mono-∙ d1 D2))

------------------------------------------------------------------------
-- Decidability of the sub-trace relation
--
-- Keeping a leading operation requires deciding equality of the two
-- operation symbols, so the decision procedure lives in a submodule
-- assuming decidable equality of operation names.

module DecSubtrace (_≟ₒ_ : DecidableEquality Op) where

  -- The relation is decided by recursion on a fuel budget bounding the
  -- combined size of the two traces. Every constructor of the relation
  -- shrinks that combined size by at least one, so the budget always
  -- suffices; the delay-free injection preserves size (`size-inj⁻`), so
  -- absorbing or spending a leading delay counts as one step too.

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
