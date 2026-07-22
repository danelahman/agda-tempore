------------------------------------------------------------------------
-- Soundness of the structural (eta/commutation) equations for the      --
-- resource modalities.                                                 --
--                                                                    --
-- `box`/`unbox` denote precomposition by an environment extension. The  --
-- eta rules `boxed-not-used`/`unbox-not-used` say a binder over an      --
-- unused variable is the identity (`fstᵐ` undoes the extension); the    --
-- commutation rules say two binders' extensions commute, which on the   --
-- environment side is `exch-ren`'s denotation `⟨ ⟨ fstᵐ∘fstᵐ , sndᵐ ⟩ , --
-- sndᵐ∘fstᵐ ⟩` reassociating the two inserted factors.                  --
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

module EquationalTheory.Soundness.Modal
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (V-rename; C-rename; unbox⇒var)

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- A boxing binder over an unused variable is the identity: the weakening
-- `⟦ wk-ren ⟧ = fstᵐ` cancels against the environment extension.

sound-boxed-not-used : ∀ {Γ A C ρ ε} → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (M : Γ ⊢C⦂ C ‼ ε)
                     → Soundᶜ== (boxed-not-used V M)
sound-boxed-not-used V M (pV , pCM) pR =
    ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (C-rename wk-ren M) pCM (renᶜ wk-ren M pR)
              ∙ C-rename-nat wk-ren M pR)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ∘ᵐ-identityʳ _

sound-unbox-not-used : ∀ {Γ A C ρ Δ} → (w : Ren (Δ ⟨ ρ ⟩) Γ) → (V : Δ ⊢V⦂ [ ρ ] A)
                     → (M : Γ ⊢C⦂ C) → Soundᶜ== (unbox-not-used w V M)
sound-unbox-not-used w V M (pV , pCM) pR =
    unbox-def w V (C-rename wk-ren M) pV pCM
  ∙ ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (C-rename wk-ren M) pCM (renᶜ wk-ren M pR)
              ∙ C-rename-nat wk-ren M pR)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ∘ᵐ-identityʳ _
