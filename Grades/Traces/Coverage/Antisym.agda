-------------------------------------------------------------------------
-- The coverage order is antisymmetric.                                --
--                                                                     --
-- Two runs that cover each other are the same run, at any cost model. --
-- The order is taken at slack zero, where `use-delay` cannot fire --  --
-- a delay has positive length -- so a demanded delay is met only by a --
-- delay, and two leading delays pin each other's length, leaving no   --
-- slack for what follows.                                             --
--                                                                     --
-- What rules out the mismatched cases is the number of operation      --
-- nodes. Coverage never buys an operation with time, so that number   --
-- is monotone along the order and `pay-op` makes it drop strictly: a  --
-- run with something banked cannot be covered back.                   --
--                                                                     --
-- This is the field `Coverage.AsOrder` fills in, and through it what  --
-- makes the normal forms of `Traces.Reduced` canonical.               --
-------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; s≤s; z≤n; _≤_)
open import Data.Nat.Properties using (1+n≰n; n≤1+n; n≮0; ≤-trans)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Coverage.Antisym
  {D : Duration} (T : TimeDomain D) (Op : Set) (costˡᵒ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; _+ᴰ_; _∸ᴰ_; _≤ᴰ_; ≤ᴰ-trans; ≤ᴰ-reflexive; +ᴰ-identityˡ)

open import Grades.Traces.Base T Op
open import Grades.Traces.Coverage T Op costˡᵒ

------------------------------------------------------------------------
-- The measure
--
-- How many operations a trace performs. A delay contributes nothing.

mutual

  ops : Trace → ℕ
  ops ε               = 0
  ops (operation _ t) = suc (ops t)
  ops (delay _ t⁻)    = ops⁻ t⁻

  ops⁻ : Trace⁻ → ℕ
  ops⁻ ε⁻               = 0
  ops⁻ (operation⁻ _ t) = suc (ops t)

ops-inj⁻ : (t⁻ : Trace⁻) → ops (inj⁻ t⁻) ≡ ops⁻ t⁻
ops-inj⁻ ε⁻               = refl
ops-inj⁻ (operation⁻ _ _) = refl

-- a covering run performs at least the operations demanded of it

ops-≼ᶜ : ∀ {k s t} → s ≼ᶜ[ k ] t → ops s ≤ ops t
ops-≼ᶜ nil                       = z≤n
ops-≼ᶜ (keep d)                  = s≤s (ops-≼ᶜ d)
ops-≼ᶜ (pay-op d)                = ≤-trans (ops-≼ᶜ d) (n≤1+n _)
ops-≼ᶜ (del-delay {t⁻ = t⁻} d)   = subst (_ ≤_) (ops-inj⁻ t⁻) (ops-≼ᶜ d)
ops-≼ᶜ (use-delay {s⁻ = s⁻} _ d) = subst (_≤ _) (ops-inj⁻ s⁻) (ops-≼ᶜ d)

------------------------------------------------------------------------
-- Delays met against an empty slack

-- banked onto an empty slack, a delay is its own slack

banked : ∀ {a b} → a ≤ᴰ 0ᴰ +ᴰ b → a ≤ᴰ b
banked {a} {b} le = ≤ᴰ-trans le (≤ᴰ-reflexive (+ᴰ-identityˡ b))

-- two delays met against each other leave nothing over

spent : {d e : D⁺} → ∣ d ∣⁺ ≤ᴰ 0ᴰ +ᴰ ∣ e ∣⁺ → ∣ e ∣⁺ ≤ᴰ 0ᴰ +ᴰ ∣ d ∣⁺
      → (0ᴰ +ᴰ ∣ e ∣⁺) ∸ᴰ ∣ d ∣⁺ ≡ 0ᴰ
spent {d} {e} le₁ le₂ =
  trans (cong (_∸ᴰ ∣ d ∣⁺) (+ᴰ-identityˡ ∣ e ∣⁺)) (∣∣⁺-∸≡0 {d} {e} (banked le₁) (banked le₂))

------------------------------------------------------------------------
-- Antisymmetry
--
-- Stated at an arbitrary pair of slacks so that the recursion under two
-- matched delays can pass on the slack they leave, which the equations
-- `j ≡ 0ᴰ`, `k ≡ 0ᴰ` pin to zero.

≼ᶜ-antisym₀ : ∀ {j k s t} → j ≡ 0ᴰ → k ≡ 0ᴰ
            → s ≼ᶜ[ j ] t → t ≼ᶜ[ k ] s → s ≡ t

-- slack zero leaves no delay to spend

≼ᶜ-antisym₀ refl refl (use-delay {d = d} le _) _ = ⊥-elim (∣∣⁺-pos d le)
≼ᶜ-antisym₀ refl refl nil (use-delay {d = d} le _) = ⊥-elim (∣∣⁺-pos d le)
≼ᶜ-antisym₀ refl refl (del-delay _) (use-delay {d = d} le _) =
  ⊥-elim (∣∣⁺-pos d le)

-- the empty demand is met only by the empty run

≼ᶜ-antisym₀ refl refl nil nil = refl

-- matched operations recurse

≼ᶜ-antisym₀ refl refl (keep d₁) (keep d₂) =
  cong (operation _) (≼ᶜ-antisym₀ refl refl d₁ d₂)

-- a banked operation drops the count strictly

≼ᶜ-antisym₀ refl refl (keep d₁) (pay-op d₂) =
  ⊥-elim (1+n≰n (≤-trans (ops-≼ᶜ d₂) (ops-≼ᶜ d₁)))
≼ᶜ-antisym₀ refl refl (pay-op d₁) q =
  ⊥-elim (1+n≰n (≤-trans (ops-≼ᶜ q) (ops-≼ᶜ d₁)))
≼ᶜ-antisym₀ refl refl (del-delay {t⁻ = t⁻} d₁) (pay-op d₂) =
  ⊥-elim (1+n≰n (≤-trans (ops-≼ᶜ d₁)
                         (subst (_≤ _) (sym (ops-inj⁻ t⁻)) (ops-≼ᶜ d₂))))

-- two leading delays: neither run has anything to bank, so both are
-- spent, and the lengths pin each other

≼ᶜ-antisym₀ refl refl
  (del-delay {e = y} {t⁻ = ε⁻} (use-delay {d = x} le₁ _))
  (del-delay {t⁻ = ε⁻} (use-delay le₂ _)) =
  cong (λ x → delay x ε⁻) (same-delay {x} {y} (banked le₁) (banked le₂))
≼ᶜ-antisym₀ refl refl
  (del-delay {t⁻ = operation⁻ _ _} _)
  (del-delay {t⁻ = ε⁻} d₂) = ⊥-elim (n≮0 (ops-≼ᶜ d₂))
≼ᶜ-antisym₀ refl refl
  (del-delay {t⁻ = ε⁻} d₁)
  (del-delay {t⁻ = operation⁻ _ _} _) = ⊥-elim (n≮0 (ops-≼ᶜ d₁))
≼ᶜ-antisym₀ refl refl
  (del-delay {t⁻ = operation⁻ _ _} (pay-op d₁))
  (del-delay {t⁻ = operation⁻ _ _} d₂) =
  ⊥-elim (1+n≰n (≤-trans (ops-≼ᶜ d₂) (ops-≼ᶜ d₁)))
≼ᶜ-antisym₀ refl refl
  (del-delay {e = y} {t⁻ = operation⁻ _ _} p₁@(use-delay {d = x} le₁ r₁))
  (del-delay {t⁻ = operation⁻ _ _} (pay-op d₂)) =
  ⊥-elim (1+n≰n (≤-trans (ops-≼ᶜ p₁) (ops-≼ᶜ d₂)))
≼ᶜ-antisym₀ refl refl
  (del-delay {e = y} {t⁻ = operation⁻ _ _} (use-delay {d = x} le₁ r₁))
  (del-delay {t⁻ = operation⁻ _ _} (use-delay le₂ r₂)) =
  cong₂ delay (same-delay {x} {y} (banked le₁) (banked le₂))
              (inj⁻-inj (≼ᶜ-antisym₀ (spent {x} {y} le₁ le₂) (spent {y} {x} le₂ le₁) r₁ r₂))

≼ᶜ-antisym : {s t : Trace} → s ≼ᶜ t → t ≼ᶜ s → s ≡ t
≼ᶜ-antisym = ≼ᶜ-antisym₀ refl refl
