------------------------------------------
-- A sub-trace preorder on timed traces --
------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (+-comm; +-assoc; ≤-refl; ≤-trans; m≤m+n; m≤n+m; +-∸-comm;
         m+n∸n≡m; m+[n∸m]≡n; m∸n+n≡m; +-monoʳ-≤; ∸-+-assoc)

open import Util.Equality

-- Sub-trace orders are parameterised by a set `Op` of operation names.

module Syntax.Grades.Traces.Subtrace (Op : Set) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺)

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
-- The delay-free injection of `Trace⁻` into `Trace`

inj⁻ : Trace⁻ → Trace
inj⁻ ε⁻               = ε
inj⁻ (operation⁻ o t) = operation o t

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
weaken {j} m (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n j m))
            (coe (sym (+-∸-comm m p)) (weaken m d'))

------------------------------------------------------------------------
-- Transitivity: the slacks add up

≼-trans : ∀ {j k s t u} → s ≼[ j ] t → t ≼[ k ] u → s ≼[ j + k ] u
≼-trans nil                       _                       = nil
-- left factor keeps an operation
≼-trans (keep d1)        (keep d2)                        = keep (≼-trans d1 d2)
≼-trans (keep d1)        (del-op d2)                      = del-op (≼-trans (keep d1) d2)
≼-trans {j} {k} (keep d1) (del-delay {e = e} d2)          =
  del-delay (coe (sym (+-assoc j k ∣ e ∣⁺))
            (≼-trans (keep d1) d2))
-- left factor deletes an operation of the middle trace
≼-trans (del-op d1)      (keep d2)                        = del-op (≼-trans d1 d2)
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
-- left factor spends slack on its own leading delay
≼-trans {j} {k} (use-delay {d = d} p d1) D2               =
  use-delay (≤-trans p (m≤m+n j k))
            (coe (sym (+-∸-comm k p)) (≼-trans d1 D2))

------------------------------------------------------------------------
-- ε is minimal: nothing but ε lies below ε at zero slack

≼ε→≡ε : {s : Trace} → s ≼ ε → s ≡ ε
≼ε→≡ε nil                       = refl
≼ε→≡ε (use-delay {d = 𝟏}    () _)
≼ε→≡ε (use-delay {d = suc⁺ n} () _)

------------------------------------------------------------------------
-- Inversion of `del-delay`: a leading delay on the right can always be
-- moved back into the slack

del-delay-inv : ∀ {k e t t⁻} → t ≼[ k ] delay e t⁻ → t ≼[ k + ∣ e ∣⁺ ] inj⁻ t⁻
del-delay-inv nil               = nil
del-delay-inv (del-delay d)     = d
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
prepend-left {c} t (use-delay {d = d} {s⁻ = ε⁻} p _)     =
  spendL d t p (≼-refl t)
prepend-left t (use-delay {s⁻ = operation⁻ o s''} _ ())

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
mono-∙ {j} {k} {s' = s'} (use-delay {d = d} {s⁻ = ε⁻} p d1) D2 =
  spendL d _ (≤-trans p (m≤m+n j k))
    (coe
           (trans (+-comm k (j ∸ ∣ d ∣⁺)) (sym (+-∸-comm k p)))
           (weaken (j ∸ ∣ d ∣⁺) (pad-left s' D2)))
mono-∙ {j} {k} (use-delay {d = d} {s⁻ = operation⁻ o s''} p d1) D2 =
  use-delay (≤-trans p (m≤m+n j k))
    (coe (sym (+-∸-comm k p)) (mono-∙ d1 D2))
