------------------------------------------------------------------------
-- Durations along the coverage order                                  --
--                                                                    --
-- A guarantee is no longer than the run that covers it, up to the     --
-- slack already banked: `s ≼ᶜ[ k ] t` gives                          --
-- `duration s ≤ duration t + k`, where both durations charge an       --
-- operation its execution time. At zero slack this is monotonicity of --
-- `duration` for `_≼ᶜ_`, which is what a time-ticks frame reads the   --
-- order through, and what makes a guarantee of a trace imply a        --
-- guarantee of the time it takes.                                    --
--                                                                    --
-- Nothing but the empty guarantee is covered by a spent run: with no  --
-- slack there is nothing to pay a named delay with, and a run that    --
-- has ended performs no operation to match. Unlike the allowance      --
-- order this needs no assumption about `costˡᵒ` -- an operation is    --
-- never bought here, at any price.                                   --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Grades.Durations using (Duration; TimeDomain)

module Grades.Traces.Coverage.Duration
  {D : Duration} (T : TimeDomain D) (Op : Set) (costˡᵒ : Op → Duration.Carrier D) where

open import Grades.Durations.Monus T as M
  using (Carrier; 0ᴰ; +-∸-assoc; +-∸-comm; ∸-+-assoc)
open M.Notation

open import Grades.Traces.Base T Op
open import Grades.Traces.Durations T Op
open import Grades.Traces.Coverage.Core T Op costˡᵒ

open Durations costˡᵒ

------------------------------------------------------------------------
-- Small arithmetic helpers

-- moving what the run's head contributes out of its duration and into
-- the slack the premise carries

lem-front : (d k e : Carrier) → d + (k + e) ≡ (e + d) + k
lem-front d k e =
  trans (cong (d +_) (+-comm k e))
        (trans (sym (+-assoc d e k)) (cong (_+ k) (+-comm d e)))

-- what the guarantee spends moves past the run's duration

lem-past : (a b e : Carrier) → a + (b + e) ≡ b + (a + e)
lem-past a b e =
  trans (sym (+-assoc a b e))
        (trans (cong (_+ e) (+-comm a b)) (+-assoc b a e))

------------------------------------------------------------------------
-- The delay-free injection preserves the duration

duration-inj⁻ : (t⁻ : Trace⁻) → duration (inj⁻ t⁻) ≡ duration⁻ t⁻
duration-inj⁻ ε⁻               = refl
duration-inj⁻ (operation⁻ o t) = refl

------------------------------------------------------------------------
-- Durations under the slack-indexed coverage relation

duration-slack : ∀ {k s t} → s ≼ᶜ[ k ] t → duration s ≤ duration t + k

-- the empty guarantee has no duration to account for
duration-slack nil = z≤n

-- a matched operation costs the same on both sides, and the premise
-- arrives with no slack, so the conclusion's is spare
duration-slack {k} (keep {o = o} {s = s} {t = t} p) =
  ≤-trans (+-monoʳ-≤ (costˡᵒ o)
                     (subst (duration s ≤_) (+-identityʳ (duration t))
                            (duration-slack p)))
          (m≤m+n (costˡᵒ o + duration t) k)

-- an unmatched operation of the run moves from its duration into the
-- slack, at its execution time
duration-slack {k} (pay-op {o = o} {t = t} p) =
  ≤-trans (duration-slack p)
          (≤-reflexive (lem-front (duration t) k (costˡᵒ o)))

-- and so does a delay of the run, at its length
duration-slack {k} (del-delay {e = e} {t⁻ = t⁻} p) =
  ≤-trans (duration-slack p)
          (≤-reflexive
            (trans (cong (_+ (k + ∣ e ∣⁺)) (duration-inj⁻ t⁻))
                   (lem-front (duration⁻ t⁻) k ∣ e ∣⁺)))

-- a named delay is paid for out of the slack, which the premise has
-- already lost
duration-slack {k} (use-delay {d = d} {s⁻ = s⁻} {t = t} le p) =
  ≤-trans (≤-reflexive (cong (∣ d ∣⁺ +_) (sym (duration-inj⁻ s⁻))))
          (≤-trans (+-monoʳ-≤ ∣ d ∣⁺ (duration-slack p))
                   (≤-reflexive
                     (trans (lem-past ∣ d ∣⁺ (duration t) (k ∸ ∣ d ∣⁺))
                            (cong (duration t +_) (m+[n∸m]≡n le)))))

------------------------------------------------------------------------
-- The duration is monotone for the coverage order

duration-≼ᶜ : {s t : Trace} → s ≼ᶜ t → duration s ≤ duration t
duration-≼ᶜ {s} {t} p =
  subst (duration s ≤_) (+-identityʳ (duration t)) (duration-slack p)

------------------------------------------------------------------------
-- Nothing but the empty guarantee is covered by a spent run

≼ᶜ-ε-inv : {s : Trace} → s ≼ᶜ ε → s ≡ ε
≼ᶜ-ε-inv nil                      = refl
≼ᶜ-ε-inv (use-delay {d = d} le _) = ⊥-elim (∣∣⁺-pos d le)
