------------------------------------------------------------------------
-- Replacing one variable, as an instance of the general theorem, and the
-- two innermost in turn.
--
-- `_[ split-pf x ↦ W ]v`/`_[ split-pf x ↦ W ]c` is `sub-split₀ (split-pf x) W` acting, and
-- `sub-env x W` is that substitution's environment morphism
-- (`sub-env-is-⟦⟧ˢ₀`), so both statements are the general ones read there.
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
module MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Core
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

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S using (wk-ren)
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename)
open import MonomorphicCalculus.Syntax.Substitution    S

open Category Cat
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
  using (renᵛ; V-rename-nat)
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Base S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence.Env S Cat Fut Pst Adj GTy Mon GE

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

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

-- Replacing the two innermost variables, the outer by `V` and the inner by
-- `W`: `W` weakened past `A` first, then `V`. The environment is the pair.

subᶜ₂ : ∀ {Γ A B C} → (M : Γ ∷ A ∷ B ⊢C⦂ C) → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
      → Paramᶜ M → Paramᵛ V → Paramᵛ W
      → Paramᶜ ((M [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c)
subᶜ₂ M V W pM pV pW =
  subᶜ (M [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
    (subᶜ M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV

C-subst₂-nat : ∀ {Γ A B C} → (M : Γ ∷ A ∷ B ⊢C⦂ C) → (V : Γ ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
             → (pM : Paramᶜ M) → (pV : Paramᵛ V) → (pW : Paramᵛ W)
             → ⟦ (M [ split-[] ↦ V-rename wk-ren W ]c) [ split-[] ↦ V ]c ⟧ᶜᵗ
                 (subᶜ₂ M V W pM pV pW)
             ≈ᵐ ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟨ ⟨ idᵐ , ⟦ V ⟧ᵛᵗ pV ⟩ᵐ , ⟦ W ⟧ᵛᵗ pW ⟩ᵐ
C-subst₂-nat M V W pM pV pW =
    C-subst-nat (M [ split-[] ↦ V-rename wk-ren W ]c) split-[] V
      (subᶜ M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)) pV
  ∙ ∘ᵐ-congˡ (  C-subst-nat M split-[] (V-rename wk-ren W) pM (renᵛ wk-ren W pW)
              ∙ ∘ᵐ-congʳ ⟨ ≈ᵐ-refl , V-rename-nat wk-ren W pW ⟩ᵐ-cong)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-identityˡ _
                , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)
