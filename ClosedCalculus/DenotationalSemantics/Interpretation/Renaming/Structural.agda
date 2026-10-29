------------------------------------------------------------------------
-- Denotations of the structural renamings.
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
open import ClosedCalculus.DenotationalSemantics.Model.Monad
module ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Structural
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

open import Data.Empty using (⊥-elim)
open import Util.Equality using (sym; trans; _≡_; refl; cong; subst; uip)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_; yes; no)


open import ClosedCalculus.Syntax.Types S
open import ClosedCalculus.Syntax.Contexts   S
open import ClosedCalculus.Syntax.Renaming   S
open import ClosedCalculus.Syntax.Renaming.Action S using (var-rename)
open import ClosedCalculus.Syntax.Renaming.Equivalence  S using (eternal?-yes)

open Category Cat
open Past Pst
open GroundEternal GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Algebra S Cat Fut Pst Adj GTy Mon GE
open import ClosedCalculus.DenotationalSemantics.Interpretation.Renaming.Extension S Cat Fut Pst Adj GTy Mon GE

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- The exchange renaming swaps the two topmost variables.

exch-ren-mor : ∀ {Γ X Y}
             → ⟦ exch-ren {Γ} {X} {Y} ⟧ʳ ≈ᵐ ⟨ mapˣᵐ fstᵐ idᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ
exch-ren-mor {Γ} {X} {Y} =
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   var-morphism-Tl-∷ {Γ ∷ X} {Y} {X} Hd _
                ∙ ∘ᵐ-congˡ (var-morphism-Hd {Γ} {X} _) ⟩ᵐ-cong)
  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
