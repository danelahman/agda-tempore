------------------------------------------------------------------------
-- A time-ticks Kripke frame for the sets of traces ordered up to the   --
-- sub-trace preorder as the resource grades.                           --
--                                                                    --
-- Worlds are time points `ℕ`. A tick world records only the elapsed   --
-- time, not which continuation trace produced it. Since the order on   --
-- this grade lets a trace of `P` shrink to any of its sub-traces, the  --
-- world may advance by *anything up to* the duration of a trace of     --
-- `P` -- a window rather than an exact tick:                           --
--                                                                    --
--   w ⊑ᵗ[ P ] w'   iff   w ≤ w' ≤ w + duration t   for some trace t    --
--                        of P                                          --
--                                                                    --
-- The window bounds are decidable and the traces form a finite set,    --
-- so the accessibility is phrased in the proof-irrelevant              --
-- `True`-of-a-decision form.                                           --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)

open import Relation.Binary.Definitions using (DecidableEquality)

open import Util.Equality

module DenotationalSemantics.Model.Example.World.SetOfTracesUpToSubtraceWithTicks
  (Op : Set) (_≟ₒ_ : DecidableEquality Op) (c : Op → ℕ) where

open import Data.Nat using (_+_; _∸_; _≤_; _≤?_; z≤n)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; +-assoc; +-comm; +-mono-≤;
         m≤m+n; m≤n+m; +-identityʳ; m+[n∸m]≡n)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties
  using (∈-cartesianProductWith⁺)
open import Data.List.Relation.Unary.Any as Any using (Any; here; any?)
open import Data.Product using (_×_; _,_)

open import Relation.Nullary.Decidable using (True; toWitness; fromWitness; _×-dec_)

open import Syntax.Grades.Traces.Base Op
open import Syntax.Grades.Traces.Durations Op
open import Syntax.Grades.Traces.Subtrace Op

open import Syntax.Grades.SetOfTracesUpToSubtrace Op _≟ₒ_
  using (traces-up-to-subtrace; _≾_)

open import DenotationalSemantics.Model.World

open Durations c
open WithDecEq _≟ₒ_ using (_∈?_; True-irr)
open DecSubtrace _≟ₒ_ using (_≼?_)

------------------------------------------------------------------------
-- The duration of a delay-free-headed trace agrees with its injection

duration-inj⁻ : (t⁻ : Trace⁻) → duration (inj⁻ t⁻) ≡ duration⁻ t⁻
duration-inj⁻ ε⁻               = refl
duration-inj⁻ (operation⁻ o t) = refl

------------------------------------------------------------------------
-- Duration monotonicity under the slack-indexed sub-trace order
--
-- A sub-trace can only drop operations and shrink delays, so its
-- duration is bounded by that of the larger trace plus the slack.

duration-≼ : ∀ {k s t} → s ≼[ k ] t → duration s ≤ duration t + k
duration-≼ nil = z≤n
duration-≼ (keep {k = k} {t = t} d) =
  ≤-trans (+-mono-≤ ≤-refl (duration-≼ d))
          (≤-reflexive (sym (+-assoc _ (duration t) k)))
duration-≼ (del-op {k = k} {o = o} {t = t} d) =
  ≤-trans (duration-≼ d)
          (+-mono-≤ (m≤n+m (duration t) (c o)) ≤-refl)
duration-≼ (del-delay {k = k} {e = e} {t⁻ = t⁻} d) =
  ≤-trans (duration-≼ d) (≤-reflexive eq)
  where
    eq : duration (inj⁻ t⁻) + (k + ∣ e ∣⁺) ≡ (∣ e ∣⁺ + duration⁻ t⁻) + k
    eq = begin
           duration (inj⁻ t⁻) + (k + ∣ e ∣⁺)
         ≡⟨ cong (_+ (k + ∣ e ∣⁺)) (duration-inj⁻ t⁻) ⟩
           duration⁻ t⁻ + (k + ∣ e ∣⁺)
         ≡⟨ cong (duration⁻ t⁻ +_) (+-comm k ∣ e ∣⁺) ⟩
           duration⁻ t⁻ + (∣ e ∣⁺ + k)
         ≡⟨ sym (+-assoc (duration⁻ t⁻) ∣ e ∣⁺ k) ⟩
           (duration⁻ t⁻ + ∣ e ∣⁺) + k
         ≡⟨ cong (_+ k) (+-comm (duration⁻ t⁻) ∣ e ∣⁺) ⟩
           (∣ e ∣⁺ + duration⁻ t⁻) + k
         ∎
duration-≼ (use-delay {k = k} {d = d} {s⁻ = s⁻} {t = t} p d') =
  ≤-trans (+-mono-≤ ≤-refl ih) (≤-reflexive eq)
  where
    ih : duration⁻ s⁻ ≤ duration t + (k ∸ ∣ d ∣⁺)
    ih = subst (_≤ duration t + (k ∸ ∣ d ∣⁺)) (duration-inj⁻ s⁻) (duration-≼ d')

    eq : ∣ d ∣⁺ + (duration t + (k ∸ ∣ d ∣⁺)) ≡ duration t + k
    eq = begin
           ∣ d ∣⁺ + (duration t + (k ∸ ∣ d ∣⁺))
         ≡⟨ sym (+-assoc ∣ d ∣⁺ (duration t) (k ∸ ∣ d ∣⁺)) ⟩
           (∣ d ∣⁺ + duration t) + (k ∸ ∣ d ∣⁺)
         ≡⟨ cong (_+ (k ∸ ∣ d ∣⁺)) (+-comm ∣ d ∣⁺ (duration t)) ⟩
           (duration t + ∣ d ∣⁺) + (k ∸ ∣ d ∣⁺)
         ≡⟨ +-assoc (duration t) ∣ d ∣⁺ (k ∸ ∣ d ∣⁺) ⟩
           duration t + (∣ d ∣⁺ + (k ∸ ∣ d ∣⁺))
         ≡⟨ cong (duration t +_) (m+[n∸m]≡n p) ⟩
           duration t + k
         ∎

-- the sub-trace order proper (no slack) bounds durations directly

duration-≼₀ : ∀ {s t} → s ≼ t → duration s ≤ duration t
duration-≼₀ {s} {t} p =
  ≤-trans (duration-≼ p) (≤-reflexive (+-identityʳ (duration t)))

------------------------------------------------------------------------
-- The frame

-- Accessibility on time ticks: reach the worlds within the window from
-- `w` up to an exact trace duration of `P` ahead.

_⊑ᵗ[_]_ : ℕ → NeTraces → ℕ → Set
w ⊑ᵗ[ P ] w' =
  True (any? (λ t → (w ≤? w') ×-dec (w' ≤? (w + duration t))) (traces P))

-- reflexivity at the unit grade `{ ε }`: the empty trace has duration
-- zero, so the singleton window `[ w , w ]` contains only `w` itself

⊑ᵗ-refl : ∀ {w} → w ⊑ᵗ[ u ] w
⊑ᵗ-refl {w} = fromWitness (here (≤-refl , m≤m+n w 0))

-- transitivity multiplies the grades: the two windows compose into the
-- window of the sequenced trace, whose duration is the sum

⊑ᵗ-trans : ∀ {P Q w w' w''}
         → w ⊑ᵗ[ P ] w' → w' ⊑ᵗ[ Q ] w'' → w ⊑ᵗ[ P · Q ] w''
⊑ᵗ-trans {P} {Q} {w} {w'} {w''} p q
  with find (toWitness p) | find (toWitness q)
... | t₁ , t₁∈P , (w≤w' , w'≤w+d₁) | t₂ , t₂∈Q , (w'≤w'' , w''≤w'+d₂) =
      fromWitness
        (Any.map
          (λ r → subst (λ z → (w ≤ w'') × (w'' ≤ w + duration z)) r
                       (≤-trans w≤w' w'≤w'' , upper))
          (∈-cartesianProductWith⁺ _∙_ t₁∈P t₂∈Q))
  where
    upper : w'' ≤ w + duration (t₁ ∙ t₂)
    upper =
      ≤-trans w''≤w'+d₂
              (≤-trans (+-mono-≤ w'≤w+d₁ ≤-refl)
                       (≤-reflexive eqU))
      where
        eqU : (w + duration t₁) + duration t₂ ≡ w + duration (t₁ ∙ t₂)
        eqU = trans (+-assoc w (duration t₁) (duration t₂))
                    (cong (w +_) (sym (duration-∙ t₁ t₂)))

-- covariance: a larger set of traces gives a larger accessibility. A
-- witnessing trace of `P` sits below some trace of `Q`, whose (larger)
-- duration widens the window while the lower bound is preserved.

⊑ᵗ-mono : ∀ {P Q w w'} → P ≾ Q → w ⊑ᵗ[ P ] w' → w ⊑ᵗ[ Q ] w'
⊑ᵗ-mono {P} {Q} {w} {w'} rel p
  with find (toWitness p)
... | t , t∈P , (w≤w' , w'≤w+dₜ)
        with find (toWitness (rel t (fromWitness t∈P)))
...     | t' , t'∈Q , t≼t' =
          fromWitness
            (Any.map
              (λ r → subst (λ z → (w ≤ w') × (w' ≤ w + duration z)) r
                           (w≤w' , upper))
              t'∈Q)
  where
    upper : w' ≤ w + duration t'
    upper = ≤-trans w'≤w+dₜ (+-mono-≤ ≤-refl (duration-≼₀ t≼t'))

-- proof irrelevance of the witnesses

⊑ᵗ-irrelevant : ∀ {P w w'} → (p q : w ⊑ᵗ[ P ] w') → p ≡ q
⊑ᵗ-irrelevant {P} {w} {w'} p q =
  True-irr (any? (λ t → (w ≤? w') ×-dec (w' ≤? (w + duration t))) (traces P)) p q

ticks : World traces-up-to-subtrace
ticks = record
  { W             = ℕ
  ; _⊑ʳ[_]_       = _⊑ᵗ[_]_
  ; ⊑ʳ-refl       = ⊑ᵗ-refl
  ; ⊑ʳ-trans      = λ {P} {Q} → ⊑ᵗ-trans {P} {Q}
  ; ⊑ʳ-mono       = λ {P} {Q} → ⊑ᵗ-mono {P} {Q}
  ; ⊑ʳ-irrelevant = λ {P} → ⊑ᵗ-irrelevant {P}
  }
