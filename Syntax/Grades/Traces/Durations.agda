------------------------------------------------------------------------
-- The per-trace duration relative to a cost on operation symbols     --
--                                                                    --
-- The cost-aware "length" of a single timed trace: a delay           --
-- contributes its length, an operation `o` its cost `c o`. This      --
-- per-trace `duration` is shared by the worst-case (`MaxDuration`)   --
-- and best-case (`MinDuration`) set-level aggregations; only the     --
-- aggregation over a set of traces differs between them.             --
------------------------------------------------------------------------

open import Util.Equality

open import Syntax.Durations using (Duration; TimeDomain)

module Syntax.Grades.Traces.Durations {D : Duration} (T : TimeDomain D) (Op : Set) where

open import Relation.Nullary using (Dec; yes; no)

open import Syntax.Grades.Traces.Base T Op
open import Syntax.Durations.Monus T
  using (Carrier; 0ᴰ; _+ᴰ_; _≤ᴰ_; _<ᴰ_; _<ᴰ?_; ≤ᴰ-refl; 0ᴰ-least; +ᴰ-assoc;
         +ᴰ-identityˡ; +ᴰ-identityʳ; +ᴰ-mono-≤; ≮0⇒≡0)

------------------------------------------------------------------------
-- Durations relative to a fixed cost on operation symbols
--
-- The development below is parameterised by the map `c` assigning to
-- each operation symbol its cost (its contribution to a duration).

module Durations (c : Op → Carrier) where

  ----------------------------------------------------------------------
  -- The duration of a trace
  --
  -- A delay contributes its length, an operation `o` its cost `c o`.

  mutual
    duration : Trace → Carrier
    duration ε               = 0ᴰ
    duration (operation o t) = c o +ᴰ duration t
    duration (delay d t)     = ∣ d ∣⁺ +ᴰ duration⁻ t

    duration⁻ : Trace⁻ → Carrier
    duration⁻ ε⁻               = 0ᴰ
    duration⁻ (operation⁻ o t) = c o +ᴰ duration t

  -- prepending a delay adds its length

  duration-prepend : (d : D⁺) (t : Trace)
                   → duration (prepend d t) ≡ ∣ d ∣⁺ +ᴰ duration t
  duration-prepend d ε               = refl
  duration-prepend d (operation o t) = refl
  duration-prepend d (delay e t)     = +ᴰ-assoc ∣ d ∣⁺ ∣ e ∣⁺ (duration⁻ t)

  -- the duration is a monoid homomorphism for sequencing of traces

  duration-∙ : (s t : Trace) → duration (s ∙ t) ≡ duration s +ᴰ duration t
  duration-∙ ε               t = sym (+ᴰ-identityˡ (duration t))
  duration-∙ (operation o s) t =
    trans (cong (c o +ᴰ_) (duration-∙ s t))
          (sym (+ᴰ-assoc (c o) (duration s) (duration t)))
  duration-∙ (delay d ε⁻)    t =
    trans (duration-prepend d t)
          (cong (_+ᴰ duration t) (sym (+ᴰ-identityʳ ∣ d ∣⁺)))
  duration-∙ (delay d (operation⁻ o s)) t =
    trans (cong (λ z → ∣ d ∣⁺ +ᴰ (c o +ᴰ z)) (duration-∙ s t))
          (trans (cong (∣ d ∣⁺ +ᴰ_) (sym (+ᴰ-assoc (c o) (duration s) (duration t))))
                 (sym (+ᴰ-assoc ∣ d ∣⁺ (c o +ᴰ duration s) (duration t))))

  -- a pure delay of `τ` has duration `τ`

  duration-⟨⟩ : (τ : Carrier) → duration ⟨ τ ⟩ ≡ τ
  duration-⟨⟩ τ = case (0ᴰ <ᴰ? τ)
    where
      case : (p : Dec (0ᴰ <ᴰ τ)) → duration (delay-of τ p) ≡ τ
      case (yes _) = +ᴰ-identityʳ τ
      case (no ¬p) = sym (≮0⇒≡0 ¬p)

------------------------------------------------------------------------
-- Comparing durations across two different costs

open Durations

-- the duration is monotone in the cost

mutual
  duration-mono : (c c' : Op → Carrier) → (∀ o → c o ≤ᴰ c' o) → (t : Trace)
                → duration c t ≤ᴰ duration c' t
  duration-mono c c' h ε               = ≤ᴰ-refl
  duration-mono c c' h (operation o t) = +ᴰ-mono-≤ (h o) (duration-mono c c' h t)
  duration-mono c c' h (delay d t)     = +ᴰ-mono-≤ ≤ᴰ-refl (duration⁻-mono c c' h t)

  duration⁻-mono : (c c' : Op → Carrier) → (∀ o → c o ≤ᴰ c' o) → (t : Trace⁻)
                 → duration⁻ c t ≤ᴰ duration⁻ c' t
  duration⁻-mono c c' h ε⁻               = ≤ᴰ-refl
  duration⁻-mono c c' h (operation⁻ o t) = +ᴰ-mono-≤ (h o) (duration-mono c c' h t)
