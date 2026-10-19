------------------------------------------------------------------------
-- Soundness of the delay-collapsing equations.                         --
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module EquationalTheory.Soundness.Delay
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

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (C-rename)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-≤; []-≤-nat; []-∘ᵐ; []-congᶠ; []-ε-nat;
                       δ; []-δ-nat)
                renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; η⊣-≤; η⊣-δ)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE using (εᵇ-η⊣-u)

-- `delay 0ᴰ M` is `M` with its (now unit-graded) lock discarded.

sound-delay-zero : ∀ {Γ A ε} → (M : Γ ⟨ of-durʳ 0ᴰ ⟩ ⊢C⦂ A ‼ ε)
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
              ∙ ∘ᵐ-congʳ (εᵇ-η⊣-u {⟦ Γ ⟧ᶜᵗˣ} of-durʳ-zero))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e (C-rename r M)) pR (renᶜ r M pM)
            ∙ sound-ε-≃ e (C-rename r M) (renᶜ r M pM)
            ∙ ∘ᵐ-congʳ (C-rename-nat r M pM)
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))))
  where
    e = ≃ₑ-sym (≃ₑ-trans (·ₑ-cong of-durᵉ-zero ≃ₑ-refl) (·ₑ-identityˡ ε))
    r = ⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ of-durʳ-zero) ∘ʳ ⟨⟩-η-ren

-- Two consecutive delays are the one delay by the sum.
--
-- `M` occurs renamed on the left and under an `ε-subst` on the right, so its
-- own certificate comes in separately (the axiom's `Midᶜ` payload).

sound-delay-delay : ∀ {Γ A τ₁ τ₂ ε} → (M : Γ ⟨ of-durʳ (τ₁ +ᴰ τ₂) ⟩ ⊢C⦂ A ‼ ε)
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
    e' = ≃ₑ-trans (·ₑ-cong of-durᵉ-plus ≃ₑ-refl) (·ₑ-assoc (of-durᵉ τ₁) (of-durᵉ τ₂) ε)
    r  = ⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ of-durʳ-plus) ∘ʳ ⟨⟩-μ-ren

    σ = ≃ᵣ⇒≿ᵣ (of-durʳ-plus {τ₁} {τ₂})

    m = ⟦ M ⟧ᶜᵗ pM

    -- The two nested transposes rebuild the comultiplication, and the
    -- syntactic lock-merge becomes the grade relaxation the model law wants.
    lock-split : [ of-durʳ τ₁ ]ᶠ ([ of-durʳ τ₂ ]ᶠ (⟨⟩-≤ {⟦ Γ ⟧ᶜᵗˣ} σ ∘ᵐ μ {⟦ Γ ⟧ᶜᵗˣ} {of-durʳ τ₂} {of-durʳ τ₁}) ∘ᵐ η⊣) ∘ᵐ η⊣
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
    delay-box : [ of-durʳ τ₁ ]ᶠ
                  ([ of-durʳ τ₂ ]ᶠ (m ∘ᵐ ⟨⟩-≤ {⟦ Γ ⟧ᶜᵗˣ} σ ∘ᵐ μ {⟦ Γ ⟧ᶜᵗˣ} {of-durʳ τ₂} {of-durʳ τ₁}) ∘ᵐ η⊣) ∘ᵐ η⊣
              ≈ᵐ δ ∘ᵐ []-≤ σ ∘ᵐ [ of-durʳ (τ₁ +ᴰ τ₂) ]ᶠ m ∘ᵐ η⊣
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
