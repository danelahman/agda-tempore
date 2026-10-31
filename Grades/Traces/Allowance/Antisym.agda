-------------------------------------------------------------------------
-- The allowance order is antisymmetric, at a positive cost model.     --
--                                                                     --
-- The statement needs `costʰⁱ` positive, a parameter here as in       --
-- `Allowance.AsOrder`: a free operation would be performed out of an  --
-- empty budget, so `ε` would permit `⌈ o ⌉` while permitting nothing  --
-- but itself, and the order would identify two different traces.      --
--                                                                     --
-- With a positive cost, `use-op` is blocked at budget zero exactly as --
-- positive delay lengths block `use-delay`, so a bound and a run that --
-- permit each other match node for node. The measure that rules out   --
-- the remaining cases is the duration: `skip-op` and `use-op` each    --
-- move it by a cost that cannot be made up.                           --
--                                                                     --
-- This is the field `Allowance.AsOrder` fills in, and through it what --
-- makes the normal forms of `Traces.Reduced` canonical.               --
-------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (1+n≰n; n≮0)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Allowance.Antisym
  {D : Duration} (T : TimeDomain D) (Op : Set) (costʰⁱ : Op → Duration.Carrier D)
  (costʰⁱ-pos : (o : Op) → ¬ (costʰⁱ o ≡ Duration.0ᴰ D)) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Base T Op
open import Grades.Traces.Durations T Op
open import Grades.Traces.Allowance T Op costʰⁱ

open Durations costʰⁱ using (duration; duration⁻)

------------------------------------------------------------------------
-- What a positive cost rules out

-- an operation fits into no room at all

no-room : (x : Op) {n : Carrier} → costʰⁱ x + n ≤ n → ⊥
no-room x {n} le =
  costʰⁱ-pos x
    (n≤0⇒n≡0 (M.+ᴰ-cancelʳ-≤ n (≤-trans le (≤-reflexive (sym (+-identityˡ n))))))

-- and is not paid for out of an empty budget

no-budget : (x : Op) → ¬ (costʰⁱ x ≤ 0ᴰ)
no-budget x le = costʰⁱ-pos x (n≤0⇒n≡0 le)

-- moving a banked delay past the head of the bound

shift : (a b c : Carrier) → a + (b + c) ≡ b + (c + a)
shift a b c = trans (lem-past a b c) (cong (b +_) (+-comm a c))

-- banked onto an empty budget, a delay is its own budget

banked : ∀ {a b} → a ≤ 0ᴰ + b → a ≤ b
banked {a} {b} le = ≤-trans le (≤-reflexive (+-identityˡ b))

slack₀ : ∀ {b s t} → s ≼ᵃ[ 0ᴰ + b ] t → duration s ≤ duration t + b
slack₀ {b} {t = t} p =
  ≤-trans (duration-slack p) (≤-reflexive (cong (duration t +_) (+-identityˡ b)))

-- two delays banked against each other leave nothing over

spent : {d e : D⁺} → ∣ d ∣⁺ ≤ 0ᴰ + ∣ e ∣⁺ → ∣ e ∣⁺ ≤ 0ᴰ + ∣ d ∣⁺
      → (0ᴰ + ∣ e ∣⁺) ∸ ∣ d ∣⁺ ≡ 0ᴰ
spent {d} {e} le₁ le₂ =
  trans (cong (_∸ ∣ d ∣⁺) (+-identityˡ ∣ e ∣⁺)) (∣∣⁺-∸≡0 {d} {e} (banked le₁) (banked le₂))

------------------------------------------------------------------------
-- Antisymmetry
--
-- Stated at an arbitrary pair of budgets so that the recursion under
-- two matched delays can pass on the budget they leave, which the
-- equations `j ≡ 0ᴰ`, `k ≡ 0ᴰ` pin to zero.

≼ᵃ-antisym₀ : ∀ {j k s t} → j ≡ 0ᴰ → k ≡ 0ᴰ
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
≼ᵃ-antisym₀ refl refl p₁@(bank-delay d₁) (skip-op {o = x} d₂) =
  ⊥-elim (no-room x (≤-trans (duration-≼ᵃ p₁) (duration-≼ᵃ d₂)))

-- two leading delays

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = y} {t⁻ = ε⁻} (use-delay {d = x} le₁ _))
  (bank-delay {t⁻ = ε⁻} (use-delay le₂ _)) =
  cong (λ x → delay x ε⁻) (same-delay {x} {y} (banked le₁) (banked le₂))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = y} {t⁻ = operation⁻ b _} (use-delay {d = x} le₁ _))
  (bank-delay {t⁻ = ε⁻} (use-delay le₂ (use-op le₃ _))) =
  ⊥-elim (no-budget b (subst (costʰⁱ b ≤_) (spent {y} {x} le₂ le₁) le₃))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = e} {t⁻ = operation⁻ b t''} (skip-op d₁))
  p₂@(bank-delay {t⁻ = ε⁻} d₂) =
  ⊥-elim (no-room b
    (subst (_≤ duration t'' + ∣ e ∣⁺)
           (shift ∣ e ∣⁺ (costʰⁱ b) (duration t''))
           (≤-trans (duration-≼ᵃ p₂) (slack₀ d₁))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = y} {t⁻ = ε⁻} (use-delay {d = x} le₁ (use-op le₃ _)))
  (bank-delay {t⁻ = operation⁻ a _} (use-delay le₂ _)) =
  ⊥-elim (no-budget a (subst (costʰⁱ a ≤_) (spent {x} {y} le₁ le₂) le₃))

≼ᵃ-antisym₀ refl refl
  p₁@(bank-delay {t⁻ = ε⁻} d₁)
  (bank-delay {e = d} {t⁻ = operation⁻ a s''} (skip-op d₂)) =
  ⊥-elim (no-room a
    (subst (_≤ duration s'' + ∣ d ∣⁺)
           (shift ∣ d ∣⁺ (costʰⁱ a) (duration s''))
           (≤-trans (duration-≼ᵃ p₁) (slack₀ d₂))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = e} {t⁻ = operation⁻ b t''} (skip-op d₁))
  p₂@(bank-delay {t⁻ = operation⁻ _ _} d₂) =
  ⊥-elim (no-room b
    (subst (_≤ duration t'' + ∣ e ∣⁺)
           (shift ∣ e ∣⁺ (costʰⁱ b) (duration t''))
           (≤-trans (duration-≼ᵃ p₂) (slack₀ d₁))))

≼ᵃ-antisym₀ refl refl
  p₁@(bank-delay {e = y} {t⁻ = operation⁻ _ _} (use-delay {d = x} le₁ r₁))
  (bank-delay {e = d} {t⁻ = operation⁻ a s''} (skip-op d₂)) =
  ⊥-elim (no-room a
    (subst (_≤ duration s'' + ∣ d ∣⁺)
           (shift ∣ d ∣⁺ (costʰⁱ a) (duration s''))
           (≤-trans (duration-≼ᵃ p₁)
                    (slack₀ d₂))))

≼ᵃ-antisym₀ refl refl
  (bank-delay {e = y} {t⁻ = operation⁻ _ _} (use-delay {d = x} le₁ r₁))
  (bank-delay {t⁻ = operation⁻ _ _} (use-delay le₂ r₂)) =
  cong₂ delay (same-delay {x} {y} (banked le₁) (banked le₂))
              (inj⁻-inj (≼ᵃ-antisym₀ (spent {x} {y} le₁ le₂) (spent {y} {x} le₂ le₁) r₁ r₂))

≼ᵃ-antisym : {s t : Trace} → s ≼ᵃ t → t ≼ᵃ s → s ≡ t
≼ᵃ-antisym = ≼ᵃ-antisym₀ refl refl
