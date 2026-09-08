------------------------------------------------------------------------
-- The moves that build allowance proofs, and what they add up to.     --
--                                                                    --
-- The relation's rules act on the *heads* of the two traces. These    --
-- lemmas lift them to the trace operations the grades are defined by: --
-- moving a leading delay of the bound into the budget and back,       --
-- prepending a delay or a whole prefix to the bound, spending budget  --
-- on a leading delay of the run, and finally monotonicity of the      --
-- trace product, which is what makes the lift of this order           --
-- compatible with the language product.                               --
--                                                                    --
-- Prefixing the bound is where this order is simple: an operation the --
-- bound offers and the run does not take is skipped outright, so a    --
-- prefix of the bound never has to be paid for.                       --
--                                                                    --
-- Monotonicity holds in the form with the second budget pinned to     --
-- zero,                                                              --
--                                                                    --
--   mono-∙ : s ≼ᵃ[ j ] s' → t ≼ᵃ[ 0 ] t' → (s ∙ t) ≼ᵃ[ j ] (s' ∙ t') --
--                                                                    --
-- and not in the budget-additive one: budget reaching the second      --
-- factor would have to cross whatever operations the first matches,   --
-- which is exactly what this order refuses. The pinned form is what   --
-- `Sets.liftˢ`'s `liftˢ-·ˢ` consumes, the lifts being taken at        --
-- `_≼ᵃ_ = _≼ᵃ[ 0 ]_`, so it is the instance the grades need.          --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m+[n∸m]≡n;
         m∸n+n≡m; +-∸-comm)

open import Util.Equality

module Syntax.Grades.Traces.Allowance.Moves (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺; ∣1+∣⁺)

open import Syntax.Grades.Traces.Allowance.Core Op cost

------------------------------------------------------------------------
-- Inversion of `bank-delay`

bank-delay-inv : ∀ {k e t t⁻} → t ≼ᵃ[ k ] delay e t⁻ → t ≼ᵃ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
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
        → t ≼ᵃ[ k + ∣ d ∣⁺ ] t' → t ≼ᵃ[ k ] prepend d t'
absorbR d ε                 hyp = bank-delay hyp
absorbR d (operation o t')  hyp = bank-delay hyp
absorbR {k} d (delay e t'⁻) hyp =
  bank-delay
    (coe (trans (+-assoc k ∣ d ∣⁺ ∣ e ∣⁺) (cong (k +_) (sym (∣∣⁺-+⁺ d e))))
         (bank-delay-inv hyp))

------------------------------------------------------------------------
-- Bumping a leading delay of the run, and spending budget on one

bumpL : ∀ {m e Z⁻ Y} (d : ℕ⁺)
      → delay e Z⁻ ≼ᵃ[ m ] Y → delay (d +⁺ e) Z⁻ ≼ᵃ[ m + ∣ d ∣⁺ ] Y
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
       → X ≼ᵃ[ c ∸ ∣ d ∣⁺ ] t → prepend d X ≼ᵃ[ c ] t
spendL d ε                 p hyp = use-delay p hyp
spendL d (operation o X')  p hyp = use-delay p hyp
spendL {c} d (delay e X'⁻) p hyp = coe (m∸n+n≡m p) (bumpL d hyp)

------------------------------------------------------------------------
-- Prepending content to the bound

pad-delay : ∀ {k t t'} (d : ℕ⁺) → t ≼ᵃ[ k ] t' → t ≼ᵃ[ k ] prepend d t'
pad-delay d D = absorbR d _ (weaken ∣ d ∣⁺ D)

pad-left : ∀ {k t t'} (c : Trace) → t ≼ᵃ[ k ] t' → t ≼ᵃ[ k ] (c ∙ t')
pad-left ε                                D = D
pad-left (operation o c')                 D = skip-op (pad-left c' D)
pad-left (delay d ε⁻)                     D = pad-delay d D
pad-left {k} (delay d (operation⁻ o c'')) D =
  bank-delay (skip-op (weaken ∣ d ∣⁺ (pad-left c'' D)))

------------------------------------------------------------------------
-- A run permitted by the empty bound prefixes harmlessly

prepend-left : ∀ {c sₐ} (t : Trace) → sₐ ≼ᵃ[ c ] ε → (sₐ ∙ t) ≼ᵃ[ c ] t
prepend-left t nil           = ≼ᵃ-refl t
prepend-left t (use-op p d') = use-op p (prepend-left t d')
prepend-left t (use-delay {d = d} {s⁻ = ε⁻} p d') =
  spendL d _ p (prepend-left t d')
prepend-left t (use-delay {d = d} {s⁻ = operation⁻ o s} p d') =
  spendL d _ p (prepend-left t d')

------------------------------------------------------------------------
-- Monotonicity of the trace product, second budget pinned to zero

mono-∙ : ∀ {j s s' t t'}
       → s ≼ᵃ[ j ] s' → t ≼ᵃ[ 0 ] t' → (s ∙ t) ≼ᵃ[ j ] (s' ∙ t')
mono-∙ {j} {s' = s'} nil D2 = pad-left s' (weaken j D2)
mono-∙ (keep d1)    D2 = keep    (mono-∙ d1 D2)
mono-∙ (skip-op d1) D2 = skip-op (mono-∙ d1 D2)
mono-∙ {j} (bank-delay {e = e} {t⁻ = ε⁻} d1) D2 =
  absorbR e _
    (coe (+-identityʳ (j + ∣ e ∣⁺)) (≼ᵃ-trans (prepend-left _ d1) D2))
mono-∙ (bank-delay {t⁻ = operation⁻ o s'''} d1) D2 = bank-delay (mono-∙ d1 D2)
mono-∙ {j} {s' = s'} (use-delay {d = d} {s⁻ = ε⁻} p d1) D2 =
  spendL d _ p (pad-left s' (weaken (j ∸ ∣ d ∣⁺) D2))
mono-∙ (use-delay {s⁻ = operation⁻ o s''} p d1) D2 = use-delay p (mono-∙ d1 D2)
mono-∙ (use-op p d1) D2 = use-op p (mono-∙ d1 D2)
