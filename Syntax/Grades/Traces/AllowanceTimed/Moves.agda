------------------------------------------------------------------------
-- The moves that build time-strict allowance proofs.                  --
--                                                                    --
-- The helpers below -- inverting a leading delay of the bound,        --
-- absorbing one into the budget, spending budget on one, padding the  --
-- bound on the left -- are the lenient order's, verbatim: none of     --
-- them touches `keep`, and it is only `keep` that this order changes. --
--                                                                    --
-- Monotonicity of the trace product is the exception. The lenient     --
-- form                                                                --
--                                                                    --
--   s ≼ᵃ[ j ] s' → t ≼ᵃ[ k ] t' → (s ∙ t) ≼ᵃ[ j + k ] (s' ∙ t')      --
--                                                                    --
-- is false here: the `k` units of budget would have to reach past a   --
-- matched operation, which is exactly what this order refuses. What   --
-- holds is the form with the second budget pinned to zero,           --
--                                                                    --
--   mono-∙ : s ≼ᵃᵗ[ j ] s' → t ≼ᵃᵗ[ 0 ] t' → (s ∙ t) ≼ᵃᵗ[ j ] (s' ∙ t')
--                                                                    --
-- which at `j := 0` is exactly what `Sets.liftˢ`'s `liftˢ-·ˢ`         --
-- consumes, the lifts being taken at `_≼ᵃᵗ_ = _≼ᵃᵗ[ 0 ]_`.           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m+[n∸m]≡n;
         m∸n+n≡m; +-∸-comm)

open import Util.Equality

module Syntax.Grades.Traces.AllowanceTimed.Moves (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺; ∣1+∣⁺)

open import Syntax.Grades.Traces.AllowanceTimed.Core Op cost

------------------------------------------------------------------------
-- Inversion of `bank-delay`

bank-delay-inv : ∀ {k e t t⁻} → t ≼ᵃᵗ[ k ] delay e t⁻ → t ≼ᵃᵗ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
bank-delay-inv nil                              = nil
bank-delay-inv (bank-delay d)                   = d
bank-delay-inv {k} {e} (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n k ∣ e ∣⁺))
            (coe (sym (+-∸-comm ∣ e ∣⁺ p)) (bank-delay-inv d'))
bank-delay-inv {k} {e} (use-op {o = o} p d')    =
  use-op (≤-trans p (m≤m+n k ∣ e ∣⁺))
         (coe (sym (+-∸-comm ∣ e ∣⁺ p)) (bank-delay-inv d'))

------------------------------------------------------------------------
-- Prepending a delay to the bound, modulo budget

absorbR : ∀ {k t} (d : ℕ⁺) (t' : Trace)
        → t ≼ᵃᵗ[ k + ∣ d ∣⁺ ] t' → t ≼ᵃᵗ[ k ] prepend d t'
absorbR d ε                 hyp = bank-delay hyp
absorbR d (operation o t')  hyp = bank-delay hyp
absorbR {k} d (delay e t'⁻) hyp =
  bank-delay
    (coe (trans (+-assoc k ∣ d ∣⁺ ∣ e ∣⁺) (cong (k +_) (sym (∣∣⁺-+⁺ d e))))
         (bank-delay-inv hyp))

------------------------------------------------------------------------
-- Bumping a leading delay of the run, and spending budget on one

bumpL : ∀ {m e Z⁻ Y} (d : ℕ⁺)
      → delay e Z⁻ ≼ᵃᵗ[ m ] Y → delay (d +⁺ e) Z⁻ ≼ᵃᵗ[ m + ∣ d ∣⁺ ] Y
bumpL {m} d (use-delay {d = e} p prem) =
  use-delay
    (subst (_≤ m + ∣ d ∣⁺) (sym (∣∣⁺-+⁺ d e)) (≤-bump ∣ d ∣⁺ ∣ e ∣⁺ m p))
    (coe (sym (trans (cong ((m + ∣ d ∣⁺) ∸_) (∣∣⁺-+⁺ d e))
                     (∸-cancel m ∣ d ∣⁺ ∣ e ∣⁺)))
         prem)
bumpL {m} d (skip-op prem)             = skip-op (bumpL d prem)
bumpL {m} d (bank-delay {e = f} prem)  =
  bank-delay (coe (lem-swap m ∣ f ∣⁺ ∣ d ∣⁺) (bumpL d prem))

spendL : ∀ {c t} (d : ℕ⁺) (X : Trace) → ∣ d ∣⁺ ≤ c
       → X ≼ᵃᵗ[ c ∸ ∣ d ∣⁺ ] t → prepend d X ≼ᵃᵗ[ c ] t
spendL d ε                 p hyp = use-delay p hyp
spendL d (operation o X')  p hyp = use-delay p hyp
spendL {c} d (delay e X'⁻) p hyp = coe (m∸n+n≡m p) (bumpL d hyp)

------------------------------------------------------------------------
-- Prepending content to the bound

pad-delay : ∀ {k t t'} (d : ℕ⁺) → t ≼ᵃᵗ[ k ] t' → t ≼ᵃᵗ[ k ] prepend d t'
pad-delay d D = absorbR d _ (weaken ∣ d ∣⁺ D)

pad-left : ∀ {k t t'} (c : Trace) → t ≼ᵃᵗ[ k ] t' → t ≼ᵃᵗ[ k ] (c ∙ t')
pad-left ε                                D = D
pad-left (operation o c')                 D = skip-op (pad-left c' D)
pad-left (delay d ε⁻)                     D = pad-delay d D
pad-left {k} (delay d (operation⁻ o c'')) D =
  bank-delay (skip-op (weaken ∣ d ∣⁺ (pad-left c'' D)))

------------------------------------------------------------------------
-- A run permitted by the empty bound prefixes harmlessly

prepend-left : ∀ {c sₐ} (t : Trace) → sₐ ≼ᵃᵗ[ c ] ε → (sₐ ∙ t) ≼ᵃᵗ[ c ] t
prepend-left t nil           = ≼ᵃᵗ-refl t
prepend-left t (use-op p d') = use-op p (prepend-left t d')
prepend-left t (use-delay {d = d} {s⁻ = ε⁻} p d') =
  spendL d _ p (prepend-left t d')
prepend-left t (use-delay {d = d} {s⁻ = operation⁻ o s} p d') =
  spendL d _ p (prepend-left t d')

------------------------------------------------------------------------
-- Monotonicity of the trace product, second budget pinned to zero

mono-∙ : ∀ {j s s' t t'}
       → s ≼ᵃᵗ[ j ] s' → t ≼ᵃᵗ[ 0 ] t' → (s ∙ t) ≼ᵃᵗ[ j ] (s' ∙ t')
mono-∙ {j} {s' = s'} nil D2 = pad-left s' (weaken j D2)
mono-∙ (keep d1)    D2 = keep    (mono-∙ d1 D2)
mono-∙ (skip-op d1) D2 = skip-op (mono-∙ d1 D2)
mono-∙ {j} (bank-delay {e = e} {t⁻ = ε⁻} d1) D2 =
  absorbR e _
    (coe (+-identityʳ (j + ∣ e ∣⁺)) (≼ᵃᵗ-trans (prepend-left _ d1) D2))
mono-∙ (bank-delay {t⁻ = operation⁻ o s'''} d1) D2 = bank-delay (mono-∙ d1 D2)
mono-∙ {j} {s' = s'} (use-delay {d = d} {s⁻ = ε⁻} p d1) D2 =
  spendL d _ p (pad-left s' (weaken (j ∸ ∣ d ∣⁺) D2))
mono-∙ (use-delay {s⁻ = operation⁻ o s''} p d1) D2 = use-delay p (mono-∙ d1 D2)
mono-∙ (use-op p d1) D2 = use-op p (mono-∙ d1 D2)
