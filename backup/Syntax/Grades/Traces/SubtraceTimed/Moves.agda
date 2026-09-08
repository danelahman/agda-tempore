------------------------------------------------------------------------
-- The moves that build time-strict sub-trace proofs.                  --
--                                                                     --
-- The helpers below -- inverting a leading delay, absorbing one into   --
-- the slack, spending slack on one, padding the run on the left -- are --
-- the lenient order's, verbatim: none of them touches `keep`, and it   --
-- is only `keep` that the time-strict order changes.                   --
--                                                                     --
-- Monotonicity of the trace product is the exception, and it has to be --
-- stated differently. The lenient order has                            --
--                                                                     --
--   s ≼[ j ] s' → t ≼[ k ] t' → (s ∙ t) ≼[ j + k ] (s' ∙ t')          --
--                                                                     --
-- and the slack-additive form is *false* here: take `s = s' = ⌈ a ⌉`,  --
-- `t = ⟨ 2 ⟩`, `t' = ε` and `k = 2`. Both premises hold, but           --
-- `operation a ⟨ 2 ⟩ ≼ᵗ[ j+2 ] operation a ε` has no derivation --     --
-- `keep` demands its tail at slack zero and `2 ≰ 0`, while `pay-op`    --
-- leaves a demand headed by an operation facing `ε`. The `k` units of  --
-- slack live *after* the match, and a match is exactly where this      --
-- order refuses to carry slack.                                        --
--                                                                     --
-- What does hold is the form with the second slack pinned to zero:     --
--                                                                     --
--   mono-∙ : s ≼ᵗ[ j ] s' → t ≼ᵗ[ 0 ] t' → (s ∙ t) ≼ᵗ[ j ] (s' ∙ t')  --
--                                                                     --
-- which at `j := 0` is exactly what `Sets.liftˢ`'s `liftˢ-·ˢ` consumes, --
-- the lifts being taken at `_≼ᵗ_ = _≼ᵗ[ 0 ]_`. Pinning the second      --
-- slack also removes every slack-swapping step the lenient proof needs, --
-- so this proof is the shorter of the two.                             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; ≤-trans; m≤m+n; m+[n∸m]≡n;
         m∸n+n≡m; +-∸-comm)

open import Data.Empty using (⊥-elim)

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceTimed.Moves (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op using (∣_∣⁺; ∣∣⁺-+⁺; ∣1+∣⁺)

-- the arithmetic helpers are about `ℕ` alone, so they are shared with
-- the lenient order rather than restated

open import Syntax.Grades.Traces.Subtrace.Core Op cost
  using (∸-cancel; ≤-bump)

open import Syntax.Grades.Traces.SubtraceTimed.Core Op cost

------------------------------------------------------------------------
-- Nothing meets a demand that names an operation once the run is spent

op-⋠ᵗ-ε : ∀ {k o s} → ¬ (operation o s ≼ᵗ[ k ] ε)
op-⋠ᵗ-ε ()

------------------------------------------------------------------------
-- Inversion of `del-delay`: a leading delay on the right can always be
-- moved back into the slack

del-delay-inv : ∀ {k e t t⁻} → t ≼ᵗ[ k ] delay e t⁻ → t ≼ᵗ[ k + ∣ e ∣⁺ ] inj⁻ t⁻
del-delay-inv nil           = nil
del-delay-inv (del-delay d) = d
del-delay-inv {k} {e} (use-delay {d = d} p d') =
  use-delay (≤-trans p (m≤m+n k ∣ e ∣⁺))
            (coe (sym (+-∸-comm ∣ e ∣⁺ p)) (del-delay-inv d'))

------------------------------------------------------------------------
-- Prepending a delay to the right-hand trace, modulo slack

absorbR : ∀ {k t} (d : ℕ⁺) (t' : Trace)
        → t ≼ᵗ[ k + ∣ d ∣⁺ ] t' → t ≼ᵗ[ k ] prepend d t'
absorbR d ε                 hyp = del-delay hyp
absorbR d (operation o t')  hyp = del-delay hyp
absorbR {k} d (delay e t'⁻) hyp =
  del-delay
    (coe (trans (+-assoc k ∣ d ∣⁺ ∣ e ∣⁺) (cong (k +_) (sym (∣∣⁺-+⁺ d e))))
         (del-delay-inv hyp))

------------------------------------------------------------------------
-- Bumping a leading delay on the left, paid for by equal extra slack

bumpL : ∀ {m e Z⁻ Y} (d : ℕ⁺)
      → delay e Z⁻ ≼ᵗ[ m ] Y → delay (d +⁺ e) Z⁻ ≼ᵗ[ m + ∣ d ∣⁺ ] Y
bumpL {m} d (use-delay {d = e} p prem) =
  use-delay
    (subst (_≤ m + ∣ d ∣⁺) (sym (∣∣⁺-+⁺ d e)) (≤-bump ∣ d ∣⁺ ∣ e ∣⁺ m p))
    (coe (sym (trans (cong ((m + ∣ d ∣⁺) ∸_) (∣∣⁺-+⁺ d e))
                     (∸-cancel m ∣ d ∣⁺ ∣ e ∣⁺)))
         prem)
bumpL {m} d (pay-op {o = o} prem) =
  pay-op (coe (lem-swap m (cost o) ∣ d ∣⁺) (bumpL d prem))
bumpL {m} d (del-delay {e = f} prem) =
  del-delay (coe (lem-swap m ∣ f ∣⁺ ∣ d ∣⁺) (bumpL d prem))

------------------------------------------------------------------------
-- Spending slack on a leading delay of `prepend d X`

spendL : ∀ {c t} (d : ℕ⁺) (X : Trace) → ∣ d ∣⁺ ≤ c
       → X ≼ᵗ[ c ∸ ∣ d ∣⁺ ] t → prepend d X ≼ᵗ[ c ] t
spendL d ε                p hyp = use-delay p hyp
spendL d (operation o X') p hyp = use-delay p hyp
spendL {c} d (delay e X'⁻) p hyp = coe (m∸n+n≡m p) (bumpL d hyp)

------------------------------------------------------------------------
-- Prepending content to the right-hand trace

pad-delay : ∀ {k t t'} (d : ℕ⁺) → t ≼ᵗ[ k ] t' → t ≼ᵗ[ k ] prepend d t'
pad-delay d D = absorbR d _ (weaken ∣ d ∣⁺ D)

pad-left : ∀ {k t t'} (c : Trace) → t ≼ᵗ[ k ] t' → t ≼ᵗ[ k ] (c ∙ t')
pad-left ε                          D = D
pad-left (operation o c')           D = del-op (pad-left c' D)
pad-left (delay d ε⁻)               D = pad-delay d D
pad-left {k} (delay d (operation⁻ o c'')) D =
  del-delay (del-op (weaken ∣ d ∣⁺ (pad-left c'' D)))

------------------------------------------------------------------------
-- A trace below ε prefixes harmlessly on the left of a product

prepend-left : ∀ {c sₐ} (t : Trace) → sₐ ≼ᵗ[ c ] ε → (sₐ ∙ t) ≼ᵗ[ c ] t
prepend-left t nil                                      = ≼ᵗ-refl t
prepend-left {c} t (use-delay {d = d} {s⁻ = ε⁻} p _)    = spendL d t p (≼ᵗ-refl t)
prepend-left t (use-delay {s⁻ = operation⁻ o s''} p d') = ⊥-elim (op-⋠ᵗ-ε d')

------------------------------------------------------------------------
-- Monotonicity of the trace product, second slack pinned to zero
--
-- Every case is the lenient proof with the slack arithmetic deleted:
-- with `k = 0` there is nothing to swap past. The `keep` case recurses
-- at slack zero, which is precisely where the time-strict rule puts it.

mono-∙ : ∀ {j s s' t t'}
       → s ≼ᵗ[ j ] s' → t ≼ᵗ[ 0 ] t' → (s ∙ t) ≼ᵗ[ j ] (s' ∙ t')
mono-∙ {j} {s' = s'} nil D2 = pad-left s' (weaken j D2)
mono-∙ (keep d1) D2 = keep (mono-∙ d1 D2)
mono-∙ (pay-op d1) D2 = pay-op (mono-∙ d1 D2)
mono-∙ {j} (del-delay {e = e} {t⁻ = ε⁻} d1) D2 =
  absorbR e _
    (coe (+-identityʳ (j + ∣ e ∣⁺)) (≼ᵗ-trans (prepend-left _ d1) D2))
mono-∙ (del-delay {t⁻ = operation⁻ o s'''} d1) D2 = del-delay (mono-∙ d1 D2)
mono-∙ {j} {s' = s'} (use-delay {d = d} {s⁻ = ε⁻} p d1) D2 =
  spendL d _ p (pad-left s' (weaken (j ∸ ∣ d ∣⁺) D2))
mono-∙ (use-delay {s⁻ = operation⁻ o s''} p d1) D2 =
  use-delay p (mono-∙ d1 D2)
