------------------------------------------------------------------------
-- The moves that build coverage proofs, and what they add up to.      --
--                                                                     --
-- The relation's rules act on the *heads* of the two traces. These    --
-- helpers lift them to the trace operations the grades are defined    --
-- by: inverting a leading delay of the run, absorbing one into the    --
-- slack, spending slack on one the guarantee names, and padding the   --
-- run on the left. None of them touches `keep`.                       --
--                                                                     --
-- Monotonicity of the trace product holds only with the second slack  --
-- pinned to zero,                                                     --
--                                                                     --
--   mono-∙ : s ≼ᶜ[ j ] s' → t ≼ᶜ[ 0 ] t' → (s ∙ t) ≼ᶜ[ j ] (s' ∙ t')  --
--                                                                     --
-- and not in the slack-additive form, slack after a match being what  --
-- this order refuses to carry. At `j := 0` the pinned form is what    --
-- `Sets.liftˢ`'s `liftˢ-·ˢ` consumes, the lifts being taken at        --
-- `_≼ᶜ_ = _≼ᶜ[ 0 ]_`, so it is the instance the grades need.          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m+[n∸m]≡n;
         m∸n+n≡m; +-∸-comm)

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.Coverage.Moves (Op : Set) (costˡᵒ : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺; ∣1+∣⁺)

-- the arithmetic helpers are about `ℕ` alone, so they are shared with
-- the allowance order rather than restated


open import Syntax.Grades.Traces.Coverage.Core Op costˡᵒ

------------------------------------------------------------------------
-- Nothing meets a demand that names an operation once the run is spent

op-⋠ᶜ-ε : ∀ {k o s} → ¬ (operation o s ≼ᶜ[ k ] ε)
op-⋠ᶜ-ε ()

------------------------------------------------------------------------
-- Inversion of `del-delay`: a leading delay on the right can always be
-- moved back into the slack

del-delay-inv : ∀ {k e t t⁻} → t ≼ᶜ[ k ] delay e t⁻ → t ≼ᶜ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
del-delay-inv nil           = nil
del-delay-inv (del-delay d) = d
del-delay-inv {k} {e} (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n k ∣ e ∣⁺))
            (coe (sym (+-∸-comm ∣ e ∣⁺ p)) (del-delay-inv d'))

------------------------------------------------------------------------
-- Prepending a delay to the right-hand trace, modulo slack

absorbR : ∀ {k t} (d : ℕ⁺) (t' : Trace)
        → t ≼ᶜ[ k + ∣ d ∣⁺ ] t' → t ≼ᶜ[ k ] prepend d t'
absorbR d ε                 hyp = del-delay hyp
absorbR d (operation o t')  hyp = del-delay hyp
absorbR {k} d (delay e t'⁻) hyp =
  del-delay
    (coe (trans (+-assoc k ∣ d ∣⁺ ∣ e ∣⁺) (cong (k +_) (sym (∣∣⁺-+⁺ d e))))
         (del-delay-inv hyp))

------------------------------------------------------------------------
-- Bumping a leading delay on the left, paid for by equal extra slack

bumpL : ∀ {m e Z⁻ Y} (d : ℕ⁺)
      → delay e Z⁻ ≼ᶜ[ m ] Y → delay (d +⁺ e) Z⁻ ≼ᶜ[ m + ∣ d ∣⁺ ] Y
bumpL {m} d (use-delay {d = e} p prem) =
  use-delay
    (subst (_≤ m + ∣ d ∣⁺) (sym (∣∣⁺-+⁺ d e)) (≤-bump ∣ d ∣⁺ ∣ e ∣⁺ m p))
    (coe (sym (trans (cong ((m + ∣ d ∣⁺) ∸_) (∣∣⁺-+⁺ d e))
                     (∸-cancel m ∣ d ∣⁺ ∣ e ∣⁺)))
         prem)
bumpL {m} d (pay-op {o = o} prem) =
  pay-op (coe (lem-swap m (costˡᵒ o) ∣ d ∣⁺) (bumpL d prem))
bumpL {m} d (del-delay {e = f} prem) =
  del-delay (coe (lem-swap m ∣ f ∣⁺ ∣ d ∣⁺) (bumpL d prem))

------------------------------------------------------------------------
-- Spending slack on a leading delay of `prepend d X`

spendL : ∀ {c t} (d : ℕ⁺) (X : Trace) → ∣ d ∣⁺ ≤ c
       → X ≼ᶜ[ c ∸ ∣ d ∣⁺ ] t → prepend d X ≼ᶜ[ c ] t
spendL d ε                p hyp = use-delay p hyp
spendL d (operation o X') p hyp = use-delay p hyp
spendL {c} d (delay e X'⁻) p hyp = coe (m∸n+n≡m p) (bumpL d hyp)

------------------------------------------------------------------------
-- Prepending content to the right-hand trace

pad-delay : ∀ {k t t'} (d : ℕ⁺) → t ≼ᶜ[ k ] t' → t ≼ᶜ[ k ] prepend d t'
pad-delay d D = absorbR d _ (weaken ∣ d ∣⁺ D)

pad-left : ∀ {k t t'} (c : Trace) → t ≼ᶜ[ k ] t' → t ≼ᶜ[ k ] (c ∙ t')
pad-left ε                          D = D
pad-left (operation o c')           D = del-op (pad-left c' D)
pad-left (delay d ε⁻)               D = pad-delay d D
pad-left {k} (delay d (operation⁻ o c'')) D =
  del-delay (del-op (weaken ∣ d ∣⁺ (pad-left c'' D)))

------------------------------------------------------------------------
-- A trace below ε prefixes harmlessly on the left of a product

prepend-left : ∀ {c sₐ} (t : Trace) → sₐ ≼ᶜ[ c ] ε → (sₐ ∙ t) ≼ᶜ[ c ] t
prepend-left t nil                                      = ≼ᶜ-refl t
prepend-left {c} t (use-delay {d = d} {s⁻ = ε⁻} p _)    = spendL d t p (≼ᶜ-refl t)
prepend-left t (use-delay {s⁻ = operation⁻ o s''} p d') = ⊥-elim (op-⋠ᶜ-ε d')

------------------------------------------------------------------------
-- Monotonicity of the trace product, second slack pinned to zero
--
-- With the second slack zero there is nothing to swap past, so no case
-- does any slack arithmetic. The `keep` case recurses at slack zero,
-- which is precisely where the rule puts it.

mono-∙ : ∀ {j s s' t t'}
       → s ≼ᶜ[ j ] s' → t ≼ᶜ[ 0 ] t' → (s ∙ t) ≼ᶜ[ j ] (s' ∙ t')
mono-∙ {j} {s' = s'} nil D2 = pad-left s' (weaken j D2)
mono-∙ (keep d1) D2 = keep (mono-∙ d1 D2)
mono-∙ (pay-op d1) D2 = pay-op (mono-∙ d1 D2)
mono-∙ {j} (del-delay {e = e} {t⁻ = ε⁻} d1) D2 =
  absorbR e _
    (coe (+-identityʳ (j + ∣ e ∣⁺)) (≼ᶜ-trans (prepend-left _ d1) D2))
mono-∙ (del-delay {t⁻ = operation⁻ o s'''} d1) D2 = del-delay (mono-∙ d1 D2)
mono-∙ {j} {s' = s'} (use-delay {d = d} {s⁻ = ε⁻} p d1) D2 =
  spendL d _ p (pad-left s' (weaken (j ∸ ∣ d ∣⁺) D2))
mono-∙ (use-delay {s⁻ = operation⁻ o s''} p d1) D2 =
  use-delay p (mono-∙ d1 D2)
