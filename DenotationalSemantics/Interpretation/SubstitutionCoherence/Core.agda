------------------------------------------------------------------------
-- Replacing one variable, as an instance of the general theorem.
--
-- `_[ split-pf x ↦ W ]v`/`_[ split-pf x ↦ W ]c` is `sub-split₀ (split-pf x) W` acting, and
-- `sub-env x W` is that substitution's environment morphism
-- (`sub-env-is-⟦⟧ˢ₀`), so both statements are the general ones read there.
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
module DenotationalSemantics.Interpretation.SubstitutionCoherence.Core
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Substitutions S

open Category Cat
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence.Env S Cat Fut Pst Adj GTy Mon GE

subᵛ : ∀ {Γ Γ₁ Γ₂ A B} → (V : Γ ⊢V⦂ B) → (s : Γ₁ ∷ A , Γ₂ split Γ)
     → (W : Γ₁ ⊢V⦂ A)
     → Paramᵛ V → Paramᵛ W → Paramᵛ (V [ s ↦ W ]v)
subᵛ V s W pV pW = subᵛˢ (sub-split₀ s W) (sub-split₀ᴾ s W pW) V pV

subᶜ : ∀ {Γ Γ₁ Γ₂ A C} → (M : Γ ⊢C⦂ C) → (s : Γ₁ ∷ A , Γ₂ split Γ)
     → (W : Γ₁ ⊢V⦂ A)
     → Paramᶜ M → Paramᵛ W → Paramᶜ (M [ s ↦ W ]c)
subᶜ M s W pM pW = subᶜˢ (sub-split₀ s W) (sub-split₀ᴾ s W pW) M pM

V-subst-nat : ∀ {Γ Γ₁ Γ₂ A B} → (V : Γ ⊢V⦂ B) → (s : Γ₁ ∷ A , Γ₂ split Γ)
            → (W : Γ₁ ⊢V⦂ A)
            → (pV : Paramᵛ V) → (pW : Paramᵛ W)
            → ⟦ V [ s ↦ W ]v ⟧ᵛᵗ (subᵛ V s W pV pW)
            ≈ᵐ ⟦ V ⟧ᵛᵗ pV ∘ᵐ sub-env s W pW
V-subst-nat V s W pV pW =
  ≈ᵐ-trans (V-subst-natˢ (sub-split₀ s W) (sub-split₀ᴾ s W pW) V pV)
           (∘ᵐ-congʳ (sub-env-is-⟦⟧ˢ₀ s W pW))

C-subst-nat : ∀ {Γ Γ₁ Γ₂ A C} → (M : Γ ⊢C⦂ C) → (s : Γ₁ ∷ A , Γ₂ split Γ)
            → (W : Γ₁ ⊢V⦂ A)
            → (pM : Paramᶜ M) → (pW : Paramᵛ W)
            → ⟦ M [ s ↦ W ]c ⟧ᶜᵗ (subᶜ M s W pM pW)
            ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ sub-env s W pW
C-subst-nat M s W pM pW =
  ≈ᵐ-trans (C-subst-natˢ (sub-split₀ s W) (sub-split₀ᴾ s W pW) M pM)
           (∘ᵐ-congʳ (sub-env-is-⟦⟧ˢ₀ s W pW))
