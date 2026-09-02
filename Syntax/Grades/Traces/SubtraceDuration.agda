------------------------------------------------------------------------
-- Durations along the sub-trace preorder                              --
--                                                                    --
-- A sub-trace is no longer than its host, up to the slack it was      --
-- granted: `s ≼[ k ] t` gives `duration s ≤ duration t + k`. At zero  --
-- slack this is monotonicity of `duration` for `_≼_`.                 --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; _+_; _∸_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-identityʳ;
         +-monoʳ-≤; +-monoˡ-≤; m≤n+m; m+[n∸m]≡n)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceDuration (Op : Set) (c : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op

open Durations c

------------------------------------------------------------------------
-- Small arithmetic helpers

-- the leading delay absorbed by `del-delay` moves to the front

lem-front : (d k e : ℕ) → d + (k + e) ≡ (e + d) + k
lem-front d k e =
  trans (cong (d +_) (+-comm k e))
        (trans (sym (+-assoc d e k)) (cong (_+ k) (+-comm d e)))

-- the leading delay spent by `use-delay` moves past the host's duration

lem-past : (a b e : ℕ) → a + (b + e) ≡ b + (a + e)
lem-past a b e =
  trans (sym (+-assoc a b e))
        (trans (cong (_+ e) (+-comm a b)) (+-assoc b a e))

------------------------------------------------------------------------
-- The delay-free injection preserves the duration

duration-inj⁻ : (t⁻ : Trace⁻) → duration (inj⁻ t⁻) ≡ duration⁻ t⁻
duration-inj⁻ ε⁻               = refl
duration-inj⁻ (operation⁻ o t) = refl

------------------------------------------------------------------------
-- Durations under the slack-indexed sub-trace relation

duration-slack : ∀ {k s t} → s ≼[ k ] t → duration s ≤ duration t + k

-- the empty trace has no duration to account for
duration-slack nil = z≤n

-- a kept operation costs the same on both sides
duration-slack {k} (keep {o = o} {t = t} p) =
  ≤-trans (+-monoʳ-≤ (c o) (duration-slack p))
          (≤-reflexive (sym (+-assoc (c o) (duration t) k)))

-- a deleted operation only adds to the host's duration
duration-slack {k} (del-op {o = o} {t = t} p) =
  ≤-trans (duration-slack p)
          (+-monoˡ-≤ k (m≤n+m (duration t) (c o)))

-- an absorbed delay is already counted in the slack the premise carries
duration-slack {k} (del-delay {e = e} {t⁻ = t⁻} p) =
  ≤-trans (duration-slack p)
          (≤-reflexive
            (trans (cong (_+ (k + ∣ e ∣⁺)) (duration-inj⁻ t⁻))
                   (lem-front (duration⁻ t⁻) k ∣ e ∣⁺)))

-- a spent delay is paid for out of the slack, which the premise loses
duration-slack {k} (use-delay {d = d} {s⁻ = s⁻} {t = t} le p) =
  ≤-trans (≤-reflexive (cong (∣ d ∣⁺ +_) (sym (duration-inj⁻ s⁻))))
          (≤-trans (+-monoʳ-≤ ∣ d ∣⁺ (duration-slack p))
                   (≤-reflexive
                     (trans (lem-past ∣ d ∣⁺ (duration t) (k ∸ ∣ d ∣⁺))
                            (cong (duration t +_) (m+[n∸m]≡n le)))))

------------------------------------------------------------------------
-- The duration is monotone for the sub-trace preorder

duration-≼ : {s t : Trace} → s ≼ t → duration s ≤ duration t
duration-≼ {s} {t} p =
  subst (duration s ≤_) (+-identityʳ (duration t)) (duration-slack p)
