------------------------------------------------------------------------
-- Strictly positive durations.                                        --
--                                                                     --
-- Delays in a timed trace carry a strictly positive duration of a     --
-- time domain, so that zero-valued delays cannot appear in a trace. A --
-- positive duration is a duration together with the verdict that it   --
-- is positive, so two are equal when their durations are, and a       --
-- literal discharges the side condition by computation.               --
--                                                                     --
-- Nothing here mentions operations, so this layer is independent of    --
-- the alphabet `Op` the rest of the trace toolkit is parameterised by. --
------------------------------------------------------------------------

open import Syntax.Durations

module Syntax.Grades.Traces.Positive {D : Duration} (T : TimeDomain D) where

open import Data.Bool.Properties using (T-irrelevant)
open import Data.Empty using (⊥; ⊥-elim)

open import Relation.Binary.Definitions
  using (DecidableEquality; Transitive; Trichotomous; tri<; tri≈; tri>)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (True; toWitness; fromWitness)

open import Util.Equality

open import Syntax.Durations.Monus T

------------------------------------------------------------------------
-- The type and its addition

record D⁺ : Set where
  constructor ⟨_⟩⁺
  field
    ∣_∣⁺   : Carrier
    {pos?} : True (0ᴰ <ᴰ? ∣_∣⁺)

open D⁺ public

-- the side condition, as a proof

∣∣⁺-pos : (d : D⁺) → 0ᴰ <ᴰ ∣ d ∣⁺
∣∣⁺-pos d = toWitness {a? = 0ᴰ <ᴰ? ∣ d ∣⁺} (pos? d)

-- a positive duration is determined by its length

∣∣⁺-inj : {d e : D⁺} → ∣ d ∣⁺ ≡ ∣ e ∣⁺ → d ≡ e
∣∣⁺-inj {_} {e} refl = cong (λ x → ⟨ ∣ e ∣⁺ ⟩⁺ {x}) (T-irrelevant _ _)

-- a duration, made positive

pos⁺ : (τ : Carrier) → 0ᴰ <ᴰ τ → D⁺
pos⁺ τ p = ⟨ τ ⟩⁺ {fromWitness p}

infixl 6 _+⁺_

_+⁺_ : D⁺ → D⁺ → D⁺
d +⁺ e = pos⁺ (∣ d ∣⁺ +ᴰ ∣ e ∣⁺)
              (<-≤-trans (∣∣⁺-pos d) (≤ᴰ-+ ∣ d ∣⁺ ∣ e ∣⁺))

∣∣⁺-+⁺ : (d e : D⁺) → ∣ d +⁺ e ∣⁺ ≡ ∣ d ∣⁺ +ᴰ ∣ e ∣⁺
∣∣⁺-+⁺ d e = refl

+⁺-assoc : (d e f : D⁺) → ((d +⁺ e) +⁺ f) ≡ (d +⁺ (e +⁺ f))
+⁺-assoc d e f = ∣∣⁺-inj (+ᴰ-assoc ∣ d ∣⁺ ∣ e ∣⁺ ∣ f ∣⁺)

+⁺-comm : (d e : D⁺) → d +⁺ e ≡ e +⁺ d
+⁺-comm d e = ∣∣⁺-inj (+ᴰ-comm ∣ d ∣⁺ ∣ e ∣⁺)

infix 4 _≟⁺_

_≟⁺_ : DecidableEquality D⁺
d ≟⁺ e with ∣ d ∣⁺ ≟ᴰ ∣ e ∣⁺
... | yes p = yes (∣∣⁺-inj p)
... | no ¬p = no λ { refl → ¬p refl }

-- a length is never zero

∣∣⁺-nz : (d : D⁺) → ¬ (∣ d ∣⁺ ≡ 0ᴰ)
∣∣⁺-nz d e = <⇒≢ (∣∣⁺-pos d) (sym e)

-- so two delays that bound each other are the same delay, and then
-- taking one from the other leaves nothing

same-delay : {d e : D⁺} → ∣ d ∣⁺ ≤ᴰ ∣ e ∣⁺ → ∣ e ∣⁺ ≤ᴰ ∣ d ∣⁺ → d ≡ e
same-delay le₁ le₂ = ∣∣⁺-inj (≤ᴰ-antisym le₁ le₂)

∣∣⁺-∸≡0 : {d e : D⁺}
        → ∣ d ∣⁺ ≤ᴰ ∣ e ∣⁺ → ∣ e ∣⁺ ≤ᴰ ∣ d ∣⁺ → ∣ e ∣⁺ ∸ᴰ ∣ d ∣⁺ ≡ 0ᴰ
∣∣⁺-∸≡0 {d} {e} le₁ le₂ = ∸-≤ le₂

------------------------------------------------------------------------
-- Cancellation
--
-- What the left cancellativity of the trace monoid rests on: prepending
-- a fixed delay is injective because adding a fixed duration is.

+⁺-cancelˡ : (d : D⁺) {e e' : D⁺} → d +⁺ e ≡ d +⁺ e' → e ≡ e'
+⁺-cancelˡ d eq = ∣∣⁺-inj (+ᴰ-cancelˡ ∣ d ∣⁺ (cong ∣_∣⁺ eq))

-- a positive duration is never equal to a strictly larger one

d≢d+⁺e : (d e : D⁺) → d +⁺ e ≡ d → ⊥
d≢d+⁺e d e eq = ∣∣⁺-nz e (+ᴰ-absorbʳ (cong ∣_∣⁺ eq))

------------------------------------------------------------------------
-- The strict total order

infix 4 _<⁺_

-- the order of the lengths, wrapped so that the delays are inferable

record _<⁺_ (d e : D⁺) : Set where
  constructor *<⁺*
  field
    <⁺-val : ∣ d ∣⁺ <ᴰ ∣ e ∣⁺

open _<⁺_ public

<⁺-trans : Transitive _<⁺_
<⁺-trans (*<⁺* p) (*<⁺* q) = *<⁺* (<-trans p q)

<⁺-cmp : Trichotomous _≡_ _<⁺_
<⁺-cmp d e with compare ∣ d ∣⁺ ∣ e ∣⁺
... | tri< p = tri< (*<⁺* p) (λ { refl → <-irrefl p })
                    (λ q → <-irrefl (<-trans p (<⁺-val q)))
... | tri≈ p = tri≈ (λ q → <⇒≢ (<⁺-val q) p) (∣∣⁺-inj p)
                    (λ q → <⇒≢ (<⁺-val q) (sym p))
... | tri> p = tri> (λ q → <-irrefl (<-trans p (<⁺-val q)))
                    (λ { refl → <-irrefl p }) (*<⁺* p)
