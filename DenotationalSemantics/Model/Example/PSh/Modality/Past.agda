------------------------------------------------------------------------
-- The context modality `⟨ ρ ⟩ A` on discretely-indexed presheaves,    --
-- given the *Kripke possibility* semantics over the graded             --
-- accessibility relation on worlds:                                    --
--                                                                    --
--   carrier (⟨ ρ ⟩ᵒ A) w  =  Σ[ w' ∈ W ] (w' ⊑ʳ[ ρ ] w) × carrier A w'  --
--                                                                    --
-- i.e. `⟨ ρ ⟩ A` holds at `w` when there is some *past* world `w'`,    --
-- reachable to `w` by spending the resource grade `ρ`, at which `A`    --
-- holds. This is a lax graded monad (unit `η`, multiplication `μ`),    --
-- packaged as an instance of `DenotationalSemantics.Model.Modality.Past`. --
--                                                                    --
-- Because the presheaves are discrete, this Σ-type is an ordinary      --
-- (non-quotiented) set. Every coherence law is either definitional or  --
-- reduces, via function extensionality, to the proof irrelevance of    --
-- the accessibility relation (`⊑ʳ-irrelevant`).                         --
------------------------------------------------------------------------

open import Syntax.Grades
open import DenotationalSemantics.Model.World

module DenotationalSemantics.Model.Example.PSh.Modality.Past (GS : GradeSystem) (Wld : World (GradeSystem.RGrade GS)) where

open import Data.Product

open import Util.Equality

open GradeSystem GS using (RGrade)
open Grade RGrade renaming (Carrier to R)
open World Wld
open import DenotationalSemantics.Model.Example.PSh.Base GS Wld

-- two-sided monotonicity of `·`

·-mono-≾ : ∀ {ρ₁ ρ₁' ρ₂ ρ₂'} → ρ₁ ≾ ρ₁' → ρ₂ ≾ ρ₂' → ρ₁ · ρ₂ ≾ ρ₁' · ρ₂'
·-mono-≾ p q = ≾-trans (·-monoˡ-≾ p) (·-monoʳ-≾ q)

-- STRUCTURE

-- Functor

⟨_⟩ᵒ : R → PSh → PSh
⟨ ρ ⟩ᵒ A = psh (λ w → Σ[ w' ∈ W ] (w' ⊑ʳ[ ρ ] w) × carrier A w')

⟨_⟩ᶠ : ∀ {A B} → (ρ : R) → A →ᵖ B → ⟨ ρ ⟩ᵒ A →ᵖ ⟨ ρ ⟩ᵒ B
⟨ ρ ⟩ᶠ f = pmap (λ { (w' , p , x) → w' , p , app f x })

-- Monotonicity for gradings (covariant: the context modality is Σ-shaped)

⟨⟩-≤ : ∀ {A ρ₁ ρ₂} → ρ₁ ≾ ρ₂ → ⟨ ρ₁ ⟩ᵒ A →ᵖ ⟨ ρ₂ ⟩ᵒ A
⟨⟩-≤ p = pmap (λ { (w' , q , x) → w' , ⊑ʳ-mono p q , x })

-- Unit

η : ∀ {A} → A →ᵖ ⟨ u ⟩ᵒ A
η = pmap (λ {w} x → w , ⊑ʳ-refl , x)

-- Multiplication (note the reversed grade order)

μ : ∀ {A ρ₁ ρ₂} → ⟨ ρ₁ ⟩ᵒ (⟨ ρ₂ ⟩ᵒ A) →ᵖ ⟨ ρ₂ · ρ₁ ⟩ᵒ A
μ = pmap (λ { (w₁ , p₁ , w₂ , p₂ , x) → w₂ , ⊑ʳ-trans p₂ p₁ , x })


-- PROPERTIES

-- ⟨_⟩ is functorial

⟨⟩-idᵖ : ∀ {A ρ} → ⟨ ρ ⟩ᶠ (idᵖ {A = A}) ≡ idᵖ
⟨⟩-idᵖ = →ᵖ-ext (λ { (w' , p , x) → refl })

⟨⟩-∘ᵖ : ∀ {A B C ρ} → (g : B →ᵖ C) → (f : A →ᵖ B)
      → ⟨ ρ ⟩ᶠ (g ∘ᵖ f) ≡ ⟨ ρ ⟩ᶠ g ∘ᵖ ⟨ ρ ⟩ᶠ f
⟨⟩-∘ᵖ g f = →ᵖ-ext (λ { (w' , p , x) → refl })

-- ⟨⟩-≤ is natural

⟨⟩-≤-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵖ B) → (p : ρ₁ ≾ ρ₂)
         → ⟨ ρ₂ ⟩ᶠ f ∘ᵖ ⟨⟩-≤ p ≡ ⟨⟩-≤ p ∘ᵖ ⟨ ρ₁ ⟩ᶠ f
⟨⟩-≤-nat f p = →ᵖ-ext (λ { (w' , q , x) → refl })

-- ⟨_⟩ is functorial in the gradings

⟨⟩-≤-refl : ∀ {A ρ} → ⟨⟩-≤ {A} (≾-refl {ρ}) ≡ idᵖ
⟨⟩-≤-refl = →ᵖ-ext (λ { (w' , p , x) → cong (λ r → w' , r , x) (⊑ʳ-irrelevant _ _) })

⟨⟩-≤-trans : ∀ {A ρ ρ' ρ''} → (p : ρ ≾ ρ') → (q : ρ' ≾ ρ'')
           → ⟨⟩-≤ {A} q ∘ᵖ ⟨⟩-≤ {A} p ≡ ⟨⟩-≤ (≾-trans p q)
⟨⟩-≤-trans p q = →ᵖ-ext (λ { (w' , r , x) → cong (λ s → w' , s , x) (⊑ʳ-irrelevant _ _) })

-- η is natural

⟨⟩-η-nat : ∀ {A B} → (f : A →ᵖ B) → ⟨ u ⟩ᶠ f ∘ᵖ η ≡ η ∘ᵖ f
⟨⟩-η-nat f = →ᵖ-ext (λ x → refl)

-- μ is natural

⟨⟩-μ-nat : ∀ {A B ρ₁ ρ₂} → (f : A →ᵖ B)
         → ⟨ ρ₂ · ρ₁ ⟩ᶠ f ∘ᵖ μ ≡ μ ∘ᵖ ⟨ ρ₁ ⟩ᶠ (⟨ ρ₂ ⟩ᶠ f)
⟨⟩-μ-nat f = →ᵖ-ext (λ { (w₁ , p₁ , w₂ , p₂ , x) → refl })

-- μ is compatible with the gradings

⟨⟩-μ-≤ : ∀ {A ρ₁ ρ₂ ρ₁' ρ₂'} → (p : ρ₁ ≾ ρ₁') → (q : ρ₂ ≾ ρ₂')
       → ⟨⟩-≤ {A} (·-mono-≾ q p) ∘ᵖ μ {A} {ρ₁} {ρ₂}
       ≡ μ {A} {ρ₁'} {ρ₂'} ∘ᵖ ⟨ ρ₁' ⟩ᶠ (⟨⟩-≤ q) ∘ᵖ ⟨⟩-≤ p
⟨⟩-μ-≤ p q =
  →ᵖ-ext (λ { (w₁ , p₁ , w₂ , p₂ , x) →
    cong (λ r → w₂ , r , x) (⊑ʳ-irrelevant _ _) })

-- Graded monad laws

⟨⟩-μ∘η≡id : ∀ {A ρ}
          → μ {A} {u} {ρ} ∘ᵖ η
          ≡ ⟨⟩-≤ (≾-reflexive (sym (·-identityʳ ρ)))
⟨⟩-μ∘η≡id = →ᵖ-ext (λ { (w' , p , x) → cong (λ r → w' , r , x) (⊑ʳ-irrelevant _ _) })

⟨⟩-μ∘Tη≡id : ∀ {A ρ}
           → μ {A} {ρ} {u} ∘ᵖ ⟨ ρ ⟩ᶠ η
           ≡ ⟨⟩-≤ (≾-reflexive (sym (·-identityˡ ρ)))
⟨⟩-μ∘Tη≡id = →ᵖ-ext (λ { (w' , p , x) → cong (λ r → w' , r , x) (⊑ʳ-irrelevant _ _) })

⟨⟩-μ∘μ≡μ∘Tμ : ∀ {A ρ₁ ρ₂ ρ₃}
            → μ {A} {ρ₂ · ρ₁} {ρ₃} ∘ᵖ μ {⟨ ρ₃ ⟩ᵒ A} {ρ₁} {ρ₂}
            ≡    ⟨⟩-≤ (≾-reflexive (·-assoc ρ₃ ρ₂ ρ₁))
              ∘ᵖ μ {A} {ρ₁} {ρ₃ · ρ₂} ∘ᵖ ⟨ ρ₁ ⟩ᶠ (μ {A} {ρ₂} {ρ₃})
⟨⟩-μ∘μ≡μ∘Tμ =
  →ᵖ-ext (λ { (w₁ , p₁ , w₂ , p₂ , w₃ , p₃ , x) →
    cong (λ r → w₃ , r , x) (⊑ʳ-irrelevant _ _) })


-- Packaging the context modality up as a `Past` instance

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Past PShCat RGrade using (Past)

PShPast : Past
PShPast = record
  { ⟨_⟩ᵒ        = ⟨_⟩ᵒ
  ; ⟨_⟩ᶠ        = ⟨_⟩ᶠ
  ; ⟨⟩-≤        = λ {A} → ⟨⟩-≤ {A}
  ; η           = η
  ; μ           = λ {A} → μ {A}
  ; ⟨⟩-idᵐ      = λ {A} → ⟨⟩-idᵖ {A}
  ; ⟨⟩-∘ᵐ       = ⟨⟩-∘ᵖ
  ; ⟨⟩-≤-nat    = ⟨⟩-≤-nat
  ; ⟨⟩-≤-refl   = λ {A} → ⟨⟩-≤-refl {A}
  ; ⟨⟩-≤-trans  = λ {A} p q → ⟨⟩-≤-trans {A} p q
  ; ⟨⟩-η-nat    = ⟨⟩-η-nat
  ; ⟨⟩-μ-nat    = ⟨⟩-μ-nat
  ; ⟨⟩-μ-≤      = λ {A} p q → ⟨⟩-μ-≤ {A} p q
  ; ⟨⟩-μ∘η≡id   = λ {A} → ⟨⟩-μ∘η≡id {A}
  ; ⟨⟩-μ∘Tη≡id  = λ {A} → ⟨⟩-μ∘Tη≡id {A}
  ; ⟨⟩-μ∘μ≡μ∘Tμ = λ {A} → ⟨⟩-μ∘μ≡μ∘Tμ {A}
  }
