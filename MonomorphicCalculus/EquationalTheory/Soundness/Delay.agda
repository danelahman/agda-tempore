------------------------------------------------------------------------
-- Soundness of the delay-collapsing equations.                       --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.EquationalTheory.Soundness.Delay
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (C-rename)
open import MonomorphicCalculus.Syntax.Substitution    S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-≤-nat; []-∘ᵐ; []-congᶠ; []-ε-nat;
                       δ; []-δ-nat)
                renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; η⊣-≤; η⊣-δ)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE using (εᵇ-η⊣-𝟏)

-- `delay 0ᴰ M` is `M` with its lock, unit-graded at `0ᴰ`, discarded.

sound-delay-zero : ∀ {Γ A ε} → (M : Γ ⟨ ιᵣ 0ᴰ ⟩ ⊢C⦂ A ! ε)
                 → Soundᶜ== (delay-zero M)
sound-delay-zero {Γ} {A} {ε} M pM pR =
    ∘ᵐ-congˡ delayᵀ-zero
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-≤-nat _ _))
                          ∙ ∘ᵐ-assoc _ _ _)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-ε-nat _))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (εᵇ-η⊣-𝟏 {⟦ Γ ⟧ᶜᵗˣ} ιᵣ-zero))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e (C-rename r M)) pR (renᶜ r M pM)
            ∙ sound-ε-≃ e (C-rename r M) (renᶜ r M pM)
            ∙ ∘ᵐ-congʳ (C-rename-nat r M pM)
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))))
  where
    e = ≃ₑ-sym (≃ₑ-trans (·ₑ-cong ιₑ-zero ≃ₑ-refl) (·ₑ-identityˡ ε))
    r = ⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ ιᵣ-zero) ∘ʳ ⟨⟩-η-ren

-- Two consecutive delays are the one delay by the sum.
--
-- `M` occurs renamed on the left and under an `ε-subst` on the right, so its
-- own certificate comes in separately (the axiom's `Midᶜ` payload).

sound-delay-delay : ∀ {Γ A τ₁ τ₂ ε} → (M : Γ ⟨ ιᵣ (τ₁ +ᴰ τ₂) ⟩ ⊢C⦂ A ! ε)
                  → Paramᶜ M → Soundᶜ== (delay-delay {τ₁ = τ₁} {τ₂ = τ₂} M)
sound-delay-delay {Γ} {A} {τ₁} {τ₂} {ε} M pM pL pR =
    ⟦⟧ᶜᵗ-irr (delay τ₁ (delay τ₂ (C-rename r M))) pL (renᶜ r M pM)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (
        C-rename-nat r M pM
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ delay-box)
  ∙ ≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
            ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congˡ (delayᵀ-plus τ₁ τ₂)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e' (delay (τ₁ +ᴰ τ₂) M)) pR pM
            ∙ sound-ε-≃ e' (delay (τ₁ +ᴰ τ₂) M) pM)
  where
    e' = ≃ₑ-trans (·ₑ-cong ιₑ-plus ≃ₑ-refl) (·ₑ-assoc (ιₑ τ₁) (ιₑ τ₂) ε)
    r  = ⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ ιᵣ-plus) ∘ʳ ⟨⟩-μ-ren

    σ = ≃ᵣ⇒≿ᵣ (ιᵣ-plus {τ₁} {τ₂})

    m = ⟦ M ⟧ᶜᵗ pM

    -- The two nested transposes rebuild the comultiplication, and the
    -- syntactic lock-merge becomes the grade relaxation the model law wants.
    lock-split : [ ιᵣ τ₁ ]ᶠ ([ ιᵣ τ₂ ]ᶠ (⟨⟩-≤ {⟦ Γ ⟧ᶜᵗˣ} σ ∘ᵐ μ {⟦ Γ ⟧ᶜᵗˣ} {ιᵣ τ₂} {ιᵣ τ₁}) ∘ᵐ η⊣) ∘ᵐ η⊣
               ≈ᵐ δ ∘ᵐ []-≤ σ ∘ᵐ η⊣
    lock-split =
        ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym η⊣-δ)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ ([]-δ-nat _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-≤ _))

    -- The same, with the delayed computation carried along under the boxes.
    delay-box : [ ιᵣ τ₁ ]ᶠ
                  ([ ιᵣ τ₂ ]ᶠ (m ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᶜᵗˣ} σ ∘ᵐ μ {⟦ Γ ⟧ᶜᵗˣ} {ιᵣ τ₂} {ιᵣ τ₁}) ∘ᵐ η⊣) ∘ᵐ η⊣
              ≈ᵐ δ ∘ᵐ []-≤ σ ∘ᵐ [ ιᵣ (τ₁ +ᴰ τ₂) ]ᶠ m ∘ᵐ η⊣
    delay-box =
        ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-congˡ ([]-∘ᵐ _ _) ∙ ∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congˡ ([]-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ lock-split
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ ([]-δ-nat _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ ([]-≤-nat _ _)
                  ∙ ∘ᵐ-assoc _ _ _)
