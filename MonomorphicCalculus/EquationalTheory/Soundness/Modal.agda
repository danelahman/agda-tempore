---------------------------------------------------------------------------
-- Soundness of the structural (eta/commutation) equations for the       --
-- resource modalities.                                                  --
--                                                                       --
-- `box`/`unbox` denote precomposition by an environment extension. The  --
-- eta rules `boxed-not-used`/`unbox-not-used` say a binder over an      --
-- unused variable is the identity (`fstᵐ` undoes the extension); the    --
-- commutation rules say two binders' extensions commute, which on the   --
-- environment side is `exch-ren`'s denotation `⟨ ⟨ fstᵐ∘fstᵐ , sndᵐ ⟩ , --
-- sndᵐ∘fstᵐ ⟩` reassociating the two inserted factors.                  --
---------------------------------------------------------------------------

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

module MonomorphicCalculus.EquationalTheory.Soundness.Modal
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

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts   S
open import MonomorphicCalculus.Syntax.Terms   S
open import MonomorphicCalculus.Syntax.Renaming   S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename)
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S using (Var)

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import MonomorphicCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- A boxing binder over an unused variable is the identity: the weakening
-- `⟦ wk-ren ⟧ = fstᵐ` cancels against the environment extension.

sound-boxed-not-used : ∀ {Γ A C ρ ε} → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A) → (M : Γ ⊢ᶜ⦂ C ! ε)
                     → Soundᶜ≡ᵗʰ (boxed-not-used V M)
sound-boxed-not-used V M (pV , pCM) pR =
    ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (C-rename wk-ren M) pCM (renᶜ wk-ren M pR)
              ∙ C-rename-nat wk-ren M pR)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ∘ᵐ-identityʳ _

sound-unbox-not-used : ∀ {Γ A A₀ C ρ₀ ρ'}
                     → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ) → (rel : ρ' ≾ᵣ ρ₀)
                     → (w : A₀ <:ᵛ A)
                     → (M : Γ ⊢ᶜ⦂ C) → Soundᶜ≡ᵗʰ (unbox-not-used x rel w M)
sound-unbox-not-used x rel w M pCM pR =
    unbox-def x rel w (C-rename wk-ren M) pCM
  ∙ ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (C-rename wk-ren M) pCM (renᶜ wk-ren M pR)
              ∙ C-rename-nat wk-ren M pR)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ∘ᵐ-identityʳ _

-- Two `unbox` nodes naming the same cell denote the same morphism: the grade
-- bound is a `_≾ᵣ_` proof and the payload witness a `_<:ᵛ_` one, both
-- irrelevant.

unbox-env-irr : ∀ {Γ A ρ} → {c c' : Var Γ ([ ρ ] A)} → c ≡ c'
              → (b : proj₁ c ≾ᵣ ρ) → (b' : proj₁ c' ≾ᵣ ρ)
              → (ε⊣ ∘ᵐ ⟨⟩-≤ b ∘ᵐ var-proj (proj₂ c))
              ≈ᵐ (ε⊣ ∘ᵐ ⟨⟩-≤ b' ∘ᵐ var-proj (proj₂ c'))
unbox-env-irr refl b b' rewrite ≾ᵣ-irrelevant b b' = ≈ᵐ-refl

unbox-cell-≈ : ∀ {Γ A A₀ C ρ₀ ρ' ρ''}
             → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ) → (x' : [ ρ₀ ] A₀ ∈[ ρ'' ] Γ)
             → (rel : ρ' ≾ᵣ ρ₀) → (rel' : ρ'' ≾ᵣ ρ₀)
             → (w w' : A₀ <:ᵛ A)
             → _≡_ {A = Var Γ ([ ρ₀ ] A₀)} (ρ' , x) (ρ'' , x')
             → (M : Γ ∷ A ⊢ᶜ⦂ C) → (pM : Paramᶜ M)
             → ⟦ unbox x rel w M ⟧ᶜᵗ pM ≈ᵐ ⟦ unbox x' rel' w' M ⟧ᶜᵗ pM

unbox-cell-≈ x x' rel rel' w w' h M pM =
    unbox-def x rel w M pM
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              , ∘ᵐ-cong (⟦⟧<:ᵛ-irr w w') (unbox-env-irr h rel rel') ⟩ᵐ-cong)
  ∙ ≈ᵐ-sym (unbox-def x' rel' w' M pM)
