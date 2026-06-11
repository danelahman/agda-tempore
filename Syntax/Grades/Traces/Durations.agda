------------------------------------------------------------------------
-- The per-trace duration relative to a cost on operation symbols     --
--                                                                    --
-- The cost-aware "length" of a single timed trace: a delay           --
-- contributes its length, an operation `o` its cost `c o`. This      --
-- per-trace `duration` is shared by the worst-case (`MaxDuration`)   --
-- and best-case (`MinDuration`) set-level aggregations; only the     --
-- aggregation over a set of traces differs between them.             --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; +-assoc; +-identityʳ; +-mono-≤)

open import Util.Equality

module Syntax.Grades.Traces.Durations (Op : Set) where

open import Syntax.Grades.Traces.Base Op

------------------------------------------------------------------------
-- The length of a positive duration as a natural number

∣_∣⁺ : ℕ⁺ → ℕ
∣ 𝟏      ∣⁺ = suc zero
∣ suc⁺ n ∣⁺ = suc ∣ n ∣⁺

-- taking the length is a monoid homomorphism `(ℕ⁺, +⁺) → (ℕ, +)`

∣∣⁺-+⁺ : (d e : ℕ⁺) → ∣ d +⁺ e ∣⁺ ≡ ∣ d ∣⁺ + ∣ e ∣⁺
∣∣⁺-+⁺ 𝟏        e = refl
∣∣⁺-+⁺ (suc⁺ d) e = cong suc (∣∣⁺-+⁺ d e)

∣1+∣⁺ : (n : ℕ) → ∣ 1+ n ∣⁺ ≡ suc n
∣1+∣⁺ zero    = refl
∣1+∣⁺ (suc n) = cong suc (∣1+∣⁺ n)

------------------------------------------------------------------------
-- Durations relative to a fixed cost on operation symbols
--
-- The development below is parameterised by the map `c` assigning to
-- each operation symbol its cost (its contribution to a duration).

module Durations (c : Op → ℕ) where

  ----------------------------------------------------------------------
  -- The duration of a trace
  --
  -- A delay contributes its length, an operation `o` its cost `c o`.

  mutual
    duration : Trace → ℕ
    duration ε               = zero
    duration (operation o t) = c o + duration t
    duration (delay d t)     = ∣ d ∣⁺ + duration⁻ t

    duration⁻ : Trace⁻ → ℕ
    duration⁻ ε⁻               = zero
    duration⁻ (operation⁻ o t) = c o + duration t

  -- prepending a delay adds its length

  duration-prepend : (d : ℕ⁺) (t : Trace)
                   → duration (prepend d t) ≡ ∣ d ∣⁺ + duration t
  duration-prepend d ε               = refl
  duration-prepend d (operation o t) = refl
  duration-prepend d (delay e t)     =
    trans (cong (_+ duration⁻ t) (∣∣⁺-+⁺ d e))
          (+-assoc ∣ d ∣⁺ ∣ e ∣⁺ (duration⁻ t))

  -- the duration is a monoid homomorphism for sequencing of traces

  duration-∙ : (s t : Trace) → duration (s ∙ t) ≡ duration s + duration t
  duration-∙ ε               t = refl
  duration-∙ (operation o s) t =
    trans (cong (c o +_) (duration-∙ s t))
          (sym (+-assoc (c o) (duration s) (duration t)))
  duration-∙ (delay d ε⁻)    t =
    trans (duration-prepend d t)
          (cong (_+ duration t) (sym (+-identityʳ ∣ d ∣⁺)))
  duration-∙ (delay d (operation⁻ o s)) t =
    trans (cong (λ z → ∣ d ∣⁺ + (c o + z)) (duration-∙ s t))
          (trans (cong (∣ d ∣⁺ +_) (sym (+-assoc (c o) (duration s) (duration t))))
                 (sym (+-assoc ∣ d ∣⁺ (c o + duration s) (duration t))))

  -- a pure delay of `n` has duration `n`

  duration-⟨⟩ : (n : ℕ) → duration ⟨ n ⟩ ≡ n
  duration-⟨⟩ zero    = refl
  duration-⟨⟩ (suc n) = trans (+-identityʳ ∣ 1+ n ∣⁺) (∣1+∣⁺ n)

------------------------------------------------------------------------
-- Comparing durations across two different costs

open Durations

-- the duration is monotone in the cost

mutual
  duration-mono : (c c' : Op → ℕ) → (∀ o → c o ≤ c' o) → (t : Trace)
                → duration c t ≤ duration c' t
  duration-mono c c' h ε               = z≤n
  duration-mono c c' h (operation o t) = +-mono-≤ (h o) (duration-mono c c' h t)
  duration-mono c c' h (delay d t)     = +-mono-≤ ≤-refl (duration⁻-mono c c' h t)

  duration⁻-mono : (c c' : Op → ℕ) → (∀ o → c o ≤ c' o) → (t : Trace⁻)
                 → duration⁻ c t ≤ duration⁻ c' t
  duration⁻-mono c c' h ε⁻               = z≤n
  duration⁻-mono c c' h (operation⁻ o t) = +-mono-≤ (h o) (duration-mono c c' h t)
