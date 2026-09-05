------------------------------------------------------------------------
-- Durations along the sub-trace preorder                              --
--                                                                    --
-- A sub-trace is no longer than its host, up to the slack it was      --
-- granted: `s ≼[ k ] t` gives `duration s ≤ duration t + k`, where    --
-- both durations charge an operation its execution time. At zero      --
-- slack this is monotonicity of `duration` for `_≼_`.                 --
--                                                                    --
-- Against a *pure delay* the bound is exact: `s ≼[ k ] ⟨ n ⟩` holds   --
-- precisely when `duration s ≤ n + k`. A time budget on the right is  --
-- therefore met by whatever mixture of delays and operations fits in  --
-- it -- this is the sense in which operations pay for time.           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-identityʳ;
         +-monoʳ-≤; +-monoˡ-≤; m≤m+n; m≤n+m; m+[n∸m]≡n; m+n≤o⇒m≤o∸n)

open import Util.Equality

module Syntax.Grades.Traces.SubtraceDuration (Op : Set) (cost : Op → ℕ) where

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op cost

open Durations cost

------------------------------------------------------------------------
-- Small arithmetic helpers

-- the leading delay absorbed by `del-delay` moves to the front

lem-front : (d k e : ℕ) → d + (k + e) ≡ (e + d) + k
lem-front d k e =
  trans (cong (d +_) (+-comm k e))
        (trans (sym (+-assoc d e k)) (cong (_+ k) (+-comm d e)))

-- reading a bound on a sum as a bound on one summand against the
-- truncated difference

+≤⇒≤∸ : ∀ {a b k} → a + b ≤ k → b ≤ k ∸ a
+≤⇒≤∸ {a} {b} {k} le = m+n≤o⇒m≤o∸n b (subst (_≤ k) (+-comm a b) le)

-- the leading delay or operation spent by `use-delay` resp. `use-op`
-- moves past the host's duration

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

-- a deleted operation only adds to the host's duration
duration-slack {k} (del-op {o = o} {t = t} p) =
  ≤-trans (duration-slack p)
          (+-monoˡ-≤ k (m≤n+m (duration t) (cost o)))

-- an absorbed delay is already counted in the slack the premise carries
duration-slack {k} (del-delay {e = e} {t⁻ = t⁻} p) =
  ≤-trans (duration-slack p)
          (≤-reflexive
            (trans (cong (_+ (k + ∣ e ∣⁺)) (duration-inj⁻ t⁻))
                   (lem-front (duration⁻ t⁻) k ∣ e ∣⁺)))

-- a spent operation is paid for out of the slack, which the premise loses
duration-slack {k} (use-op {o = o} {s = s} {t = t} le p) =
  ≤-trans (+-monoʳ-≤ (cost o) (duration-slack p))
          (≤-reflexive
            (trans (lem-past (cost o) (duration t) (k ∸ cost o))
                   (cong (duration t +_) (m+[n∸m]≡n le))))

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
-- The converse, against the empty host
--
-- With nothing on the right to match against, every event of the trace
-- has to be paid for out of the slack, and the slack suffices exactly
-- when it covers the trace's duration.

mutual

  ≼-ε : ∀ {k} (s : Trace) → duration s ≤ k → s ≼[ k ] ε
  ≼-ε ε               le = nil
  ≼-ε (operation o s) le =
    use-op (≤-trans (m≤m+n (cost o) (duration s)) le)
           (≼-ε s (+≤⇒≤∸ le))
  ≼-ε (delay d s⁻)    le =
    use-delay (≤-trans (m≤m+n ∣ d ∣⁺ (duration⁻ s⁻)) le)
              (≼-ε⁻ s⁻ (+≤⇒≤∸ le))

  ≼-ε⁻ : ∀ {k} (s⁻ : Trace⁻) → duration⁻ s⁻ ≤ k → inj⁻ s⁻ ≼[ k ] ε
  ≼-ε⁻ ε⁻               le = nil
  ≼-ε⁻ (operation⁻ o s) le =
    use-op (≤-trans (m≤m+n (cost o) (duration s)) le)
           (≼-ε s (+≤⇒≤∸ le))

------------------------------------------------------------------------
-- The characterisation against a pure delay
--
-- A trace lies below the pure delay `⟨ n ⟩` at slack `k` exactly when
-- its duration -- operations charged at their execution time -- fits in
-- `n + k`.

≼-⟨⟩ : ∀ {k} (s : Trace) (n : ℕ) → duration s ≤ n + k → s ≼[ k ] ⟨ n ⟩
≼-⟨⟩     s zero    le = ≼-ε s le
≼-⟨⟩ {k} s (suc m) le =
  del-delay (≼-ε s (subst (duration s ≤_) eq le))
  where
    eq : suc m + k ≡ k + ∣ 1+ m ∣⁺
    eq = trans (+-comm (suc m) k) (cong (k +_) (sym (∣1+∣⁺ m)))

⟨⟩-≼ : ∀ {k n} {s : Trace} → s ≼[ k ] ⟨ n ⟩ → duration s ≤ n + k
⟨⟩-≼ {k} {n} {s} p =
  subst (λ z → duration s ≤ z + k) (duration-⟨⟩ n) (duration-slack p)

------------------------------------------------------------------------
-- An operation fits inside a pure time budget exactly when the budget
-- covers its execution time

⌈⌉-≼-⟨⟩ : (o : Op) (n : ℕ) → cost o ≤ n → ⌈ o ⌉ ≼ ⟨ n ⟩
⌈⌉-≼-⟨⟩ o n le =
  ≼-⟨⟩ ⌈ o ⌉ n
       (subst₂ _≤_ (sym (+-identityʳ (cost o))) (sym (+-identityʳ n)) le)

⌈⌉-≼-⟨⟩⁻ : (o : Op) (n : ℕ) → ⌈ o ⌉ ≼ ⟨ n ⟩ → cost o ≤ n
⌈⌉-≼-⟨⟩⁻ o n p =
  subst₂ _≤_ (+-identityʳ (cost o)) (+-identityʳ n) (⟨⟩-≼ {s = ⌈ o ⌉} p)
