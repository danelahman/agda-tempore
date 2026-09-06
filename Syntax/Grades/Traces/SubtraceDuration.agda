------------------------------------------------------------------------
-- Durations along the sub-trace preorder                              --
--                                                                    --
-- A demand is no longer than the run that meets it, up to the slack   --
-- already banked: `s ≼[ k ] t` gives `duration s ≤ duration t + k`,    --
-- where both durations charge an operation its execution time. At     --
-- zero slack this is monotonicity of `duration` for `_≼_`.            --
--                                                                    --
-- Against a demanded *pure delay* the bound is exact: `⟨ n ⟩ ≼[ k ] t` --
-- holds precisely when `n ≤ duration t + k`. A demand for time is     --
-- therefore met by whatever mixture of delays and operations elapsed  --
-- -- this is the sense in which time spent pays for time demanded.    --
------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-identityʳ;
         +-monoʳ-≤; +-monoˡ-≤; m≤m+n; m≤n+m; m+[n∸m]≡n; m+n≤o⇒m≤o∸n)

open import Relation.Nullary using (¬_)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceDuration (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op cost

open Durations cost

------------------------------------------------------------------------
-- Small arithmetic helpers

-- the leading delay absorbed by `del-delay` moves to the front

-- moving what the run's head contributes out of its duration and into
-- the slack the premise carries

shift : (a b k : ℕ) → (a + b) + k ≡ b + (k + a)
shift a b k =
  trans (cong (_+ k) (+-comm a b))
        (trans (+-assoc b a k) (cong (b +_) (+-comm a k)))

lem-front : (d k e : ℕ) → d + (k + e) ≡ (e + d) + k
lem-front d k e =
  trans (cong (d +_) (+-comm k e))
        (trans (sym (+-assoc d e k)) (cong (_+ k) (+-comm d e)))

-- reading a bound on a sum as a bound on one summand against the
-- truncated difference

+≤⇒≤∸ : ∀ {a b k} → a + b ≤ k → b ≤ k ∸ a
+≤⇒≤∸ {a} {b} {k} le = m+n≤o⇒m≤o∸n b (subst (_≤ k) (+-comm a b) le)

-- the leading delay spent by `use-delay` moves past the run's duration

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
  ≤-trans (+-monoʳ-≤ (cost o) (duration-slack p))
          (≤-reflexive (sym (+-assoc (cost o) (duration t) k)))

-- a banked operation moves its execution time from the slack the
-- premise carries into the run's own duration
duration-slack {k} (pay-op {o = o} {t = t} p) =
  ≤-trans (duration-slack p)
          (≤-reflexive
            (trans (sym (+-assoc (duration t) k (cost o)))
                   (trans (+-comm (duration t + k) (cost o))
                          (sym (+-assoc (cost o) (duration t) k)))))

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

------------------------------------------------------------------------
-- Nothing but the empty demand is met by a spent run
--
-- With nothing left of the run, a demanded operation has nothing to
-- match and a demanded delay has no slack to be paid from.

∣∣⁺-pos : (d : ℕ⁺) → ¬ (∣ d ∣⁺ ≤ zero)
∣∣⁺-pos 𝟏        ()
∣∣⁺-pos (suc⁺ d) ()

≼-ε-inv : {s : Trace} → s ≼ ε → s ≡ ε
≼-ε-inv nil                     = refl
≼-ε-inv (use-delay {d = d} p _) = ⊥-elim (∣∣⁺-pos d p)

------------------------------------------------------------------------
-- The characterisation against a demanded pure delay
--
-- A demand for `⟨ n ⟩` -- that `n` units of time have passed, however
-- spent -- is met by a run at slack `k` exactly when the run's
-- duration, operations charged at their execution time, reaches `n`
-- given `k`.

⟨⟩-≼ : ∀ {k n} {t : Trace} → ⟨ n ⟩ ≼[ k ] t → n ≤ duration t + k
⟨⟩-≼ {k} {n} {t} p =
  subst (λ z → z ≤ duration t + k) (duration-⟨⟩ n) (duration-slack p)

mutual

  ≼-⟨⟩ : ∀ {k} (n : ℕ) (t : Trace) → n ≤ duration t + k → ⟨ n ⟩ ≼[ k ] t
  ≼-⟨⟩ zero        t              le = nil
  ≼-⟨⟩ {k} (suc m) ε              le =
    use-delay (subst (_≤ k) (sym (∣1+∣⁺ m)) le) nil
  ≼-⟨⟩ {k} (suc m) (operation o t) le =
    pay-op (≼-⟨⟩ (suc m) t (≤-trans le (≤-reflexive (shift (cost o) (duration t) k))))
  ≼-⟨⟩ {k} (suc m) (delay e t⁻)   le =
    del-delay (≼-⟨⟩⁻ (suc m) t⁻
                (≤-trans le (≤-reflexive (shift ∣ e ∣⁺ (duration⁻ t⁻) k))))

  ≼-⟨⟩⁻ : ∀ {k} (n : ℕ) (t⁻ : Trace⁻)
        → n ≤ duration⁻ t⁻ + k → ⟨ n ⟩ ≼[ k ] inj⁻ t⁻
  ≼-⟨⟩⁻ zero        t⁻               le = nil
  ≼-⟨⟩⁻ {k} (suc m) ε⁻               le =
    use-delay (subst (_≤ k) (sym (∣1+∣⁺ m)) le) nil
  ≼-⟨⟩⁻ {k} (suc m) (operation⁻ o t) le =
    pay-op (≼-⟨⟩ (suc m) t (≤-trans le (≤-reflexive (shift (cost o) (duration t) k))))

------------------------------------------------------------------------
-- A demand for time is met by a single operation exactly when that
-- operation takes at least as long
--
-- This is the side condition on `ρ' = { ⌈ o ⌉ }` discharging
-- `ρ = { ⟨ n ⟩ }` in the `unbox` rule.

dur-⌈⌉ : (o : Op) → duration ⌈ o ⌉ + zero ≡ cost o
dur-⌈⌉ o = trans (+-identityʳ (cost o + zero)) (+-identityʳ (cost o))

⟨⟩-≼-⌈⌉ : (n : ℕ) (o : Op) → n ≤ cost o → ⟨ n ⟩ ≼ ⌈ o ⌉
⟨⟩-≼-⌈⌉ n o le = ≼-⟨⟩ n ⌈ o ⌉ (≤-trans le (≤-reflexive (sym (dur-⌈⌉ o))))

⟨⟩-≼-⌈⌉⁻ : (n : ℕ) (o : Op) → ⟨ n ⟩ ≼ ⌈ o ⌉ → n ≤ cost o
⟨⟩-≼-⌈⌉⁻ n o p =
  ≤-trans (⟨⟩-≼ {t = ⌈ o ⌉} p) (≤-reflexive (dur-⌈⌉ o))
