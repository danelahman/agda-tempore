------------------------------------------------------------------------
-- Durations along the allowance order                                 --
--                                                                    --
-- A permitted run is no longer than the bound that permits it, up to  --
-- the budget already banked: `s ≼ᵃ[ k ] t` gives                     --
-- `duration s ≤ duration t + k`, where both durations charge an       --
-- operation its execution time. At zero budget this is monotonicity   --
-- of `duration` for `_≼ᵃ_`, which is what a time-ticks frame reads    --
-- the order through.                                                 --
--                                                                    --
-- The bound is one-way: a bound may take longer than everything it    --
-- permits, since its operations may be skipped and its delays left    --
-- unspent.                                                           --
--                                                                    --
-- The module closes with the inversion that nothing but the empty run --
-- is permitted by the empty bound. That needs every operation to      --
-- cost something -- a free operation could be paid for out of no      --
-- budget at all -- so the positivity of `cost` is taken as an         --
-- argument where it is used, and it is what the grade's zero-product  --
-- law ultimately rests on.                                           --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-identityʳ;
         +-monoʳ-≤; +-monoˡ-≤; m≤m+n; m≤n+m; m+[n∸m]≡n; n≤0⇒n≡0)

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.Allowance.Duration (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Allowance.Core Op cost

open Durations cost

------------------------------------------------------------------------
-- Small arithmetic helpers

-- moving what the bound's head contributes out of its duration and into
-- the budget the premise carries

lem-front : (d k e : ℕ) → d + (k + e) ≡ (e + d) + k
lem-front d k e =
  trans (cong (d +_) (+-comm k e))
        (trans (sym (+-assoc d e k)) (cong (_+ k) (+-comm d e)))

-- what the run's head spends moves past the bound's duration

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
-- Durations under the budget-indexed allowance relation

duration-slack : ∀ {k s t} → s ≼ᵃ[ k ] t → duration s ≤ duration t + k

-- the empty run has no duration to account for
duration-slack nil = z≤n

-- an operation the bound names costs the same on both sides
duration-slack {k} (keep {o = o} {t = t} p) =
  ≤-trans (+-monoʳ-≤ (cost o) (duration-slack p))
          (≤-reflexive (sym (+-assoc (cost o) (duration t) k)))

-- one the run skips only makes the bound longer
duration-slack {k} (skip-op {o = o} {t = t} p) =
  ≤-trans (duration-slack p)
          (+-monoˡ-≤ k (m≤n+m (duration t) (cost o)))

-- a delay of the bound moves from its duration into the budget
duration-slack {k} (bank-delay {e = e} {t⁻ = t⁻} p) =
  ≤-trans (duration-slack p)
          (≤-reflexive
            (trans (cong (_+ (k + ∣ e ∣⁺)) (duration-inj⁻ t⁻))
                   (lem-front (duration⁻ t⁻) k ∣ e ∣⁺)))

-- a delay of the run is paid for out of the budget, which the premise
-- has already lost
duration-slack {k} (use-delay {d = d} {s⁻ = s⁻} {t = t} le p) =
  ≤-trans (≤-reflexive (cong (∣ d ∣⁺ +_) (sym (duration-inj⁻ s⁻))))
          (≤-trans (+-monoʳ-≤ ∣ d ∣⁺ (duration-slack p))
                   (≤-reflexive
                     (trans (lem-past ∣ d ∣⁺ (duration t) (k ∸ ∣ d ∣⁺))
                            (cong (duration t +_) (m+[n∸m]≡n le)))))

-- and so is an operation the bound does not name, at its execution time
duration-slack {k} (use-op {o = o} {t = t} le p) =
  ≤-trans (+-monoʳ-≤ (cost o) (duration-slack p))
          (≤-reflexive
            (trans (lem-past (cost o) (duration t) (k ∸ cost o))
                   (cong (duration t +_) (m+[n∸m]≡n le))))

------------------------------------------------------------------------
-- The duration is monotone for the allowance order

duration-≼ᵃ : {s t : Trace} → s ≼ᵃ t → duration s ≤ duration t
duration-≼ᵃ {s} {t} p =
  subst (duration s ≤_) (+-identityʳ (duration t)) (duration-slack p)

------------------------------------------------------------------------
-- Nothing but the empty run is permitted by the empty bound
--
-- With no budget there is nothing to pay a delay or an unnamed
-- operation with, and the empty bound names nothing to keep or skip.

0≮0 : ¬ (0 < 0)
0≮0 ()

∣∣⁺-pos : (d : ℕ⁺) → ¬ (∣ d ∣⁺ ≤ zero)
∣∣⁺-pos 𝟏        ()
∣∣⁺-pos (suc⁺ d) ()

≼ᵃ-ε-inv : (∀ o → 0 < cost o) → {s : Trace} → s ≼ᵃ ε → s ≡ ε
≼ᵃ-ε-inv pos nil                      = refl
≼ᵃ-ε-inv pos (use-delay {d = d} le _) = ⊥-elim (∣∣⁺-pos d le)
≼ᵃ-ε-inv pos (use-op {o = o} le _)    =
  ⊥-elim (0≮0 (subst (0 <_) (n≤0⇒n≡0 le) (pos o)))
