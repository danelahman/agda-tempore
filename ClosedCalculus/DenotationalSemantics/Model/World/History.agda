-------------------------------------------------------------------------
-- The history frame of a grade over timed traces.                     --
--                                                                     --
-- A world is a timed trace, the run observed so far. A trace is read  --
-- in the grade by reading each operation by its grade and each delay  --
-- by `of-dur`, and sequencing:                                        --
--                                                                     --
--   ⟦ ε ⟧ = u     ⟦ o · s ⟧ = opᵍ o · ⟦ s ⟧     ⟦ d · s ⟧ = of-dur d · ⟦ s ⟧
--                                                                     --
-- a monoid morphism up to `≃`. A grade `ρ` reaches the histories      --
-- extending the current one by a continuation it admits:              --
--                                                                     --
--   w ⊑ʰ[ ρ ] w'   iff   Σ[ s ] w ∙ s ≡ w'  and  ⟦ s ⟧ ≾ ρ            --
--                                                                     --
-- The laws hold at every grade: reflexivity is the empty trace,       --
-- transitivity the morphism and monotonicity of the product,          --
-- covariance transitivity of the order, and proof irrelevance left    --
-- cancellation of traces with irrelevance of the order. Every world   --
-- reached extends the current one, and `⊤` reaches every extension.   --
-------------------------------------------------------------------------

open import Grades.Durations using (Duration; TimeDomain)
open import Grades.Base using (Grade)

module ClosedCalculus.DenotationalSemantics.Model.World.History
  {D : Duration} (T : TimeDomain D) (Op : Set)
  (G : Grade D) (opᵍ : Op → Grade.Carrier G) where

open import Data.Product using (Σ; Σ-syntax; _×_; _,_)

open import Util.Equality

open import Grades.Traces.Base T Op
  using (Trace; Trace⁻; ε; operation; delay; ε⁻; operation⁻; inj⁻;
         _∙_; prepend; ∙-assoc; ∙-identityʳ; ∙-cancelˡ; D⁺; ∣_∣⁺; _+⁺_)

open import ClosedCalculus.DenotationalSemantics.Model.World

open Grade G

------------------------------------------------------------------------
-- The grade of a trace

⟦_⟧ᵗ : Trace → Carrier
⟦_⟧⁻ : Trace⁻ → Carrier

⟦ ε             ⟧ᵗ = u
⟦ operation o s ⟧ᵗ = opᵍ o · ⟦ s ⟧ᵗ
⟦ delay d s     ⟧ᵗ = of-dur ∣ d ∣⁺ · ⟦ s ⟧⁻

⟦ ε⁻             ⟧⁻ = u
⟦ operation⁻ o s ⟧⁻ = opᵍ o · ⟦ s ⟧ᵗ

⟦inj⁻⟧ : ∀ s → ⟦ inj⁻ s ⟧ᵗ ≡ ⟦ s ⟧⁻
⟦inj⁻⟧ ε⁻               = refl
⟦inj⁻⟧ (operation⁻ o s) = refl

-- prepending a delay

⟦prepend⟧ : ∀ d s → ⟦ prepend d s ⟧ᵗ ≃ of-dur ∣ d ∣⁺ · ⟦ s ⟧ᵗ
⟦prepend⟧ d ε               = ≃-refl
⟦prepend⟧ d (operation o s) = ≃-refl
⟦prepend⟧ d (delay e s)     =
  ≃-trans (·-cong of-dur-plus ≃-refl) (·-assoc (of-dur ∣ d ∣⁺) (of-dur ∣ e ∣⁺) ⟦ s ⟧⁻)

-- reading is a monoid morphism

⟦∙⟧ : ∀ s t → ⟦ s ∙ t ⟧ᵗ ≃ ⟦ s ⟧ᵗ · ⟦ t ⟧ᵗ
⟦∙⟧ ε                          t = ≃-sym (·-identityˡ ⟦ t ⟧ᵗ)
⟦∙⟧ (operation o s)            t =
  ≃-trans (·-cong ≃-refl (⟦∙⟧ s t)) (≃-sym (·-assoc (opᵍ o) ⟦ s ⟧ᵗ ⟦ t ⟧ᵗ))
⟦∙⟧ (delay d ε⁻)               t =
  ≃-trans (⟦prepend⟧ d t) (·-cong (≃-sym (·-identityʳ (of-dur ∣ d ∣⁺))) ≃-refl)
⟦∙⟧ (delay d (operation⁻ o s)) t =
  ≃-trans (·-cong ≃-refl (≃-trans (·-cong ≃-refl (⟦∙⟧ s t))
                                  (≃-sym (·-assoc (opᵍ o) ⟦ s ⟧ᵗ ⟦ t ⟧ᵗ))))
          (≃-sym (·-assoc (of-dur ∣ d ∣⁺) (opᵍ o · ⟦ s ⟧ᵗ) ⟦ t ⟧ᵗ))

------------------------------------------------------------------------
-- Accessibility on histories

infix 5 _⊑ʰ[_]_

record _⊑ʰ[_]_ (w : Trace) (ρ : Carrier) (w' : Trace) : Set where
  constructor mkʰ
  field
    cont     : Trace                 -- continuation
    extends  : w ∙ cont ≡ w'         -- `w'` extends `w`
    admitted : ⟦ cont ⟧ᵗ ≾ ρ         -- by a run the grade admits

open _⊑ʰ[_]_ public

⊑ʰ-refl : ∀ {w} → w ⊑ʰ[ u ] w
⊑ʰ-refl {w} = mkʰ ε (∙-identityʳ w) ≾-refl

⊑ʰ-trans : ∀ {ρ₁ ρ₂ w w' w''} → w ⊑ʰ[ ρ₁ ] w' → w' ⊑ʰ[ ρ₂ ] w'' → w ⊑ʰ[ ρ₁ · ρ₂ ] w''
⊑ʰ-trans {w = w} (mkʰ s₁ e₁ p₁) (mkʰ s₂ e₂ p₂) =
  mkʰ (s₁ ∙ s₂)
      (trans (sym (∙-assoc w s₁ s₂)) (trans (cong (_∙ s₂) e₁) e₂))
      (≾-trans (≃⇒≾ (⟦∙⟧ s₁ s₂)) (≾-trans (·-monoˡ-≾ p₁) (·-monoʳ-≾ p₂)))

⊑ʰ-mono : ∀ {ρ₁ ρ₂ w w'} → ρ₁ ≾ ρ₂ → w ⊑ʰ[ ρ₁ ] w' → w ⊑ʰ[ ρ₂ ] w'
⊑ʰ-mono r (mkʰ s e p) = mkʰ s e (≾-trans p r)

⊑ʰ-irrelevant : ∀ {ρ w w'} → (p q : w ⊑ʰ[ ρ ] w') → p ≡ q
⊑ʰ-irrelevant {w = w} (mkʰ s refl p) (mkʰ s' e' p') with ∙-cancelˡ w e'
... | refl with uip {p = e'} {q = refl} | ≾-irrelevant p p'
... | refl | refl = refl

------------------------------------------------------------------------
-- The frame

histories : World G
histories = record
  { W            = Trace
  ; _⊑[_]_       = _⊑ʰ[_]_
  ; ⊑-refl       = ⊑ʰ-refl
  ; ⊑-trans      = ⊑ʰ-trans
  ; ⊑-mono       = ⊑ʰ-mono
  ; ⊑-irrelevant = ⊑ʰ-irrelevant
  }

------------------------------------------------------------------------
-- Forward, and the top reaches every extension

⊑ʰ-forward : ∀ {ρ w w'} → w ⊑ʰ[ ρ ] w' → Σ[ s ∈ Trace ] w ∙ s ≡ w'
⊑ʰ-forward (mkʰ s e _) = s , e

⊑ʰ-⊤ : ∀ w s → w ⊑ʰ[ ⊤ ] w ∙ s
⊑ʰ-⊤ w s = mkʰ s refl (≾-⊤ ⟦ s ⟧ᵗ)
