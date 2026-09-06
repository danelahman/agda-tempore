------------------------------------------------------------------------
-- The moves that build sub-trace proofs, and what they add up to.     --
--                                                                     --
-- The relation's constructors act on the *heads* of the two traces.    --
-- These lemmas lift them to the trace operations the grades are        --
-- defined by: prepending a delay or a whole prefix to either side,     --
-- moving a right-hand delay back into the slack, and finally the       --
-- monotonicity of the trace product, which is what makes the           --
-- sub-trace lift of the order compatible with the language product.    --
--                                                                     --
-- The section on operation-free runs records the asymmetry the order   --
-- is built around: a demanded operation is met only by that operation  --
-- occurring, so no amount of elapsed time stands in for it.            --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; ≤-trans; m≤m+n; m+[n∸m]≡n; m∸n+n≡m; +-∸-comm)

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.Subtrace.Moves (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺; ∣1+∣⁺)

open import Syntax.Grades.Traces.Subtrace.Core Op cost

------------------------------------------------------------------------
-- Time does not pay for operations
--
-- A demanded operation is discharged only by `keep`, which needs that
-- very operation to occur in the run. So a run that performs none --
-- however long it idles -- meets no demand that names one. This is the
-- asymmetry the order is built around, and the converse of `use-delay`
-- letting a demanded delay be met by any elapsed time.

data Op-free : Trace → Set where
  ε-free   : Op-free ε
  del-free : ∀ {d} → Op-free (delay d ε⁻)

-- nothing meets a demand that names an operation once the run is spent

op-⋠-ε : ∀ {k o s} → ¬ (operation o s ≼[ k ] ε)
op-⋠-ε ()

op-⋠ : ∀ {k o s t} → Op-free t → ¬ (operation o s ≼[ k ] t)
op-⋠ ε-free   d               = op-⋠-ε d
op-⋠ del-free (del-delay d)   = op-⋠-ε d

-- in particular, no pure delay meets a demand for an operation

⌈⌉-⋠⟨⟩ : ∀ {k} (o : Op) (n : ℕ) → ¬ (⌈ o ⌉ ≼[ k ] ⟨ n ⟩)
⌈⌉-⋠⟨⟩ o zero    = op-⋠ ε-free
⌈⌉-⋠⟨⟩ o (suc n) = op-⋠ del-free

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
bumpL {m} d (pay-op {o = o} prem)   =
  pay-op (coe (lem-swap m (cost o) ∣ d ∣⁺) (bumpL d prem))
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
prepend-left t (use-delay {s⁻ = operation⁻ o s''} p d')  =
  ⊥-elim (op-⋠-ε d')

------------------------------------------------------------------------
-- Monotonicity of the trace product (the slacks add up)

mono-∙ : ∀ {j k s s' t t'}
       → s ≼[ j ] s' → t ≼[ k ] t' → (s ∙ t) ≼[ j + k ] (s' ∙ t')
mono-∙ {j} {k} {s' = s'} nil D2 =
  coe (+-comm k j) (weaken j (pad-left s' D2))
mono-∙ (keep d1)   D2 = keep   (mono-∙ d1 D2)
mono-∙ {j} {k} (pay-op {o = o} d1) D2 =
  pay-op (coe (lem-swap j (cost o) k) (mono-∙ d1 D2))
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
