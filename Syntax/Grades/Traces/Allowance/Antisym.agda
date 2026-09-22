------------------------------------------------------------------------
-- The allowance order is antisymmetric, at a positive cost model.     --
--                                                                    --
-- Positivity of `costʰⁱ` is what the statement needs, and it is taken --
-- as a parameter exactly as `Allowance.AsOrder` takes it: a free      --
-- operation would be performed out of an empty budget, so `ε` would   --
-- permit `⌈ o ⌉` while permitting nothing but itself, and the order   --
-- would identify two different traces.                                --
--                                                                    --
-- With a positive cost, `use-op` is blocked at budget zero exactly as --
-- positive delay lengths block `use-delay`, so a bound and a run that --
-- permit each other match node for node. The measure that rules out   --
-- the remaining cases is the duration: `skip-op` and `use-op` each    --
-- move it by a cost that cannot be made up.                           --
--                                                                    --
-- This is the field `Allowance.AsOrder` fills in, and through it what --
-- makes the normal forms of `Traces.Reduced` canonical.               --
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; _<_)
open import Data.Nat.Properties using (≤-trans; 1+n≰n; +-monoˡ-≤; +-comm; n≮0)

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.Allowance.Antisym
  (Op : Set) (costʰⁱ : Op → ℕ)
  (costʰⁱ-pos : (o : Op) → 0 < costʰⁱ o) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Allowance Op costʰⁱ

open Durations costʰⁱ using (duration; duration⁻)

------------------------------------------------------------------------
-- What a positive cost rules out

-- an operation fits into no room at all

no-room : (x : Op) {n : ℕ} → costʰⁱ x + n ≤ n → ⊥
no-room x {n} le = 1+n≰n (≤-trans (+-monoˡ-≤ n (costʰⁱ-pos x)) le)

-- and is not paid for out of an empty budget

no-budget : (x : Op) → ¬ (costʰⁱ x ≤ 0)
no-budget x le = n≮0 (≤-trans (costʰⁱ-pos x) le)

-- moving a banked delay past the head of the bound

shift : (a b c : ℕ) → a + (b + c) ≡ b + (c + a)
shift a b c = trans (lem-past a b c) (cong (b +_) (+-comm a c))

------------------------------------------------------------------------
-- Antisymmetry
--
-- Stated at an arbitrary pair of budgets so that the recursion under
-- two matched delays can pass on the budget they leave, which the
-- equations `j ≡ 0`, `k ≡ 0` pin to zero.

≼ᵃ-antisym₀ : ∀ {j k s t} → j ≡ 0 → k ≡ 0
            → s ≼ᵃ[ j ] t → t ≼ᵃ[ k ] s → s ≡ t

-- at budget zero nothing can be spent

≼ᵃ-antisym₀ refl refl (use-delay {d = d} le _) _ = ⊥-elim (∣∣⁺-pos d le)
≼ᵃ-antisym₀ refl refl (use-op {o = x} le _) _ = ⊥-elim (no-budget x le)
≼ᵃ-antisym₀ refl refl nil (use-delay {d = d} le _) = ⊥-elim (∣∣⁺-pos d le)
≼ᵃ-antisym₀ refl refl nil (use-op {o = x} le _) = ⊥-elim (no-budget x le)
≼ᵃ-antisym₀ refl refl (keep _) (use-op {o = x} le _) = ⊥-elim (no-budget x le)
≼ᵃ-antisym₀ refl refl (bank-delay _) (use-delay {d = d} le _) =
  ⊥-elim (∣∣⁺-pos d le)

-- the empty bound permits only the empty run

≼ᵃ-antisym₀ refl refl nil nil = refl

-- matched operations recurse

≼ᵃ-antisym₀ refl refl (keep d₁) (keep d₂) =
  cong (operation _) (≼ᵃ-antisym₀ refl refl d₁ d₂)

-- a skipped operation costs the bound time the run cannot make up

≼ᵃ-antisym₀ refl refl (keep {o = x} d₁) (skip-op d₂) =
  ⊥-elim (no-room x (≤-trans (duration-≼ᵃ d₂) (duration-≼ᵃ d₁)))
≼ᵃ-antisym₀ refl refl (skip-op {o = x} d₁) q =
  ⊥-elim (no-room x (≤-trans (duration-≼ᵃ q) (duration-≼ᵃ d₁)))
≼ᵃ-antisym₀ refl refl (bank-delay d₁) (skip-op {o = x} d₂) =
  ⊥-elim (no-room x (≤-trans (duration-≼ᵃ (bank-delay d₁)) (duration-≼ᵃ d₂)))

-- two leading delays

≼ᵃ-antisym₀ refl refl
  (bank-delay {t⁻ = ε⁻} (use-delay le₁ _))
  (bank-delay {t⁻ = ε⁻} (use-delay le₂ _)) =
  cong (λ x → delay x ε⁻) (same-delay le₁ le₂)

≼ᵃ-antisym₀ refl refl
  (bank-delay {t⁻ = operation⁻ b _} (use-delay le₁ _))
  (bank-delay {t⁻ = ε⁻} (use-delay le₂ (use-op le₃ _))) =
  ⊥-elim (no-budget b (subst (costʰⁱ b ≤_) (∣∣⁺-∸≡0 le₂ le₁) le₃))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = e} {t⁻ = operation⁻ b t''} (skip-op d₁))
  (bank-delay {t⁻ = ε⁻} d₂) =
  ⊥-elim (no-room b
    (subst (_≤ duration t'' + ∣ e ∣⁺)
           (shift ∣ e ∣⁺ (costʰⁱ b) (duration t''))
           (≤-trans (duration-≼ᵃ (bank-delay d₂)) (duration-slack d₁))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {t⁻ = ε⁻} (use-delay le₁ (use-op le₃ _)))
  (bank-delay {t⁻ = operation⁻ a _} (use-delay le₂ _)) =
  ⊥-elim (no-budget a (subst (costʰⁱ a ≤_) (∣∣⁺-∸≡0 le₁ le₂) le₃))

≼ᵃ-antisym₀ refl refl
  (bank-delay {t⁻ = ε⁻} d₁)
  (bank-delay {e = d} {t⁻ = operation⁻ a s''} (skip-op d₂)) =
  ⊥-elim (no-room a
    (subst (_≤ duration s'' + ∣ d ∣⁺)
           (shift ∣ d ∣⁺ (costʰⁱ a) (duration s''))
           (≤-trans (duration-≼ᵃ (bank-delay d₁)) (duration-slack d₂))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = e} {t⁻ = operation⁻ b t''} (skip-op d₁))
  (bank-delay {t⁻ = operation⁻ _ _} d₂) =
  ⊥-elim (no-room b
    (subst (_≤ duration t'' + ∣ e ∣⁺)
           (shift ∣ e ∣⁺ (costʰⁱ b) (duration t''))
           (≤-trans (duration-≼ᵃ (bank-delay d₂)) (duration-slack d₁))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {t⁻ = operation⁻ _ _} (use-delay le₁ r₁))
  (bank-delay {e = d} {t⁻ = operation⁻ a s''} (skip-op d₂)) =
  ⊥-elim (no-room a
    (subst (_≤ duration s'' + ∣ d ∣⁺)
           (shift ∣ d ∣⁺ (costʰⁱ a) (duration s''))
           (≤-trans (duration-≼ᵃ (bank-delay (use-delay le₁ r₁)))
                    (duration-slack d₂))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {t⁻ = operation⁻ _ _} (use-delay le₁ r₁))
  (bank-delay {t⁻ = operation⁻ _ _} (use-delay le₂ r₂)) =
  cong₂ delay (same-delay le₁ le₂)
              (inj⁻-inj (≼ᵃ-antisym₀ (∣∣⁺-∸≡0 le₁ le₂) (∣∣⁺-∸≡0 le₂ le₁) r₁ r₂))

≼ᵃ-antisym : {s t : Trace} → s ≼ᵃ t → t ≼ᵃ s → s ≡ t
≼ᵃ-antisym = ≼ᵃ-antisym₀ refl refl
