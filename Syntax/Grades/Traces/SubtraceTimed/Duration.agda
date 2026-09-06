------------------------------------------------------------------------
-- Durations along the time-strict sub-trace preorder.                 --
--                                                                     --
-- Everything here is inherited. `≼ᵗ→≼` embeds the time-strict order in --
-- the lenient one, so every *upper* bound the lenient order proves --   --
-- a demand is no longer than the run meeting it, nothing but the empty --
-- demand is met by a spent run -- holds here verbatim.                 --
--                                                                     --
-- The converse direction has to be redone rather than transported, and --
-- it goes through unchanged: a demand for a *pure delay* names no      --
-- operation, so `keep` -- the one rule the time-strict order alters -- --
-- never fires, and the two orders literally coincide on such demands.  --
-- Time demanded as time is therefore still met by whatever mixture of  --
-- delays and operations elapsed.                                       --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-identityʳ)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceTimed.Duration
  (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.SubtraceTimed.Core Op cost

open import Syntax.Grades.Traces.SubtraceDuration Op cost
  using (duration-slack; duration-≼; ≼-ε-inv; shift; dur-⌈⌉)

open Durations cost

------------------------------------------------------------------------
-- Upper bounds, transported along the embedding

duration-slackᵗ : ∀ {k s t} → s ≼ᵗ[ k ] t → duration s ≤ duration t + k
duration-slackᵗ p = duration-slack (≼ᵗ→≼ p)

duration-≼ᵗ : {s t : Trace} → s ≼ᵗ t → duration s ≤ duration t
duration-≼ᵗ p = duration-≼ (≼ᵗ→≼ p)

≼ᵗ-ε-inv : {s : Trace} → s ≼ᵗ ε → s ≡ ε
≼ᵗ-ε-inv p = ≼-ε-inv (≼ᵗ→≼ p)

------------------------------------------------------------------------
-- The characterisation against a demanded pure delay
--
-- The demand `⟨ n ⟩` contains no operation, so the derivation below
-- never reaches `keep`: it is the lenient proof, and it is a proof of
-- the time-strict order for exactly that reason.

⟨⟩-≼ᵗ : ∀ {k n} {t : Trace} → ⟨ n ⟩ ≼ᵗ[ k ] t → n ≤ duration t + k
⟨⟩-≼ᵗ {k} {n} {t} p =
  subst (λ z → z ≤ duration t + k) (duration-⟨⟩ n) (duration-slackᵗ p)

mutual

  ≼ᵗ-⟨⟩ : ∀ {k} (n : ℕ) (t : Trace) → n ≤ duration t + k → ⟨ n ⟩ ≼ᵗ[ k ] t
  ≼ᵗ-⟨⟩ zero        t              le = nil
  ≼ᵗ-⟨⟩ {k} (suc m) ε              le =
    use-delay (subst (_≤ k) (sym (∣1+∣⁺ m)) le) nil
  ≼ᵗ-⟨⟩ {k} (suc m) (operation o t) le =
    pay-op (≼ᵗ-⟨⟩ (suc m) t
             (≤-trans le (≤-reflexive (shift (cost o) (duration t) k))))
  ≼ᵗ-⟨⟩ {k} (suc m) (delay e t⁻)   le =
    del-delay (≼ᵗ-⟨⟩⁻ (suc m) t⁻
                (≤-trans le (≤-reflexive (shift ∣ e ∣⁺ (duration⁻ t⁻) k))))

  ≼ᵗ-⟨⟩⁻ : ∀ {k} (n : ℕ) (t⁻ : Trace⁻)
         → n ≤ duration⁻ t⁻ + k → ⟨ n ⟩ ≼ᵗ[ k ] inj⁻ t⁻
  ≼ᵗ-⟨⟩⁻ zero        t⁻               le = nil
  ≼ᵗ-⟨⟩⁻ {k} (suc m) ε⁻               le =
    use-delay (subst (_≤ k) (sym (∣1+∣⁺ m)) le) nil
  ≼ᵗ-⟨⟩⁻ {k} (suc m) (operation⁻ o t) le =
    pay-op (≼ᵗ-⟨⟩ (suc m) t
             (≤-trans le (≤-reflexive (shift (cost o) (duration t) k))))

------------------------------------------------------------------------
-- A demand for time is met by a single operation exactly when that
-- operation takes at least as long
--
-- Unchanged from the lenient order, and for the same reason: one
-- operation on the right is banked, never matched.

⟨⟩-≼ᵗ-⌈⌉ : (n : ℕ) (o : Op) → n ≤ cost o → ⟨ n ⟩ ≼ᵗ ⌈ o ⌉
⟨⟩-≼ᵗ-⌈⌉ n o le = ≼ᵗ-⟨⟩ n ⌈ o ⌉ (≤-trans le (≤-reflexive (sym (dur-⌈⌉ o))))

⟨⟩-≼ᵗ-⌈⌉⁻ : (n : ℕ) (o : Op) → ⟨ n ⟩ ≼ᵗ ⌈ o ⌉ → n ≤ cost o
⟨⟩-≼ᵗ-⌈⌉⁻ n o p =
  ≤-trans (⟨⟩-≼ᵗ {t = ⌈ o ⌉} p) (≤-reflexive (dur-⌈⌉ o))
