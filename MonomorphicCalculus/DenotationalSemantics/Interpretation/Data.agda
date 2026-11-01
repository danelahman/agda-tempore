------------------------------------------------------------------------
-- Data as values, and comparisons of data.                           --
--                                                                    --
-- The value a datum embeds as (`⌈_⌉`) denotes the datum's point,     --
-- constant in the context (`⟦⌈⌉⟧`). A comparison of two values       --
-- denoting points of data denotes the boolean constant of the        --
-- relation's truth on the data's order (`sound-cmp`): the semantic   --
-- content of `CMP` and of the equational theory's comparison β law.  --
------------------------------------------------------------------------

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import MonomorphicCalculus.DenotationalSemantics.Model.Category
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Future
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Past
open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundTypes
open import MonomorphicCalculus.DenotationalSemantics.Model.GroundEternal
open import MonomorphicCalculus.DenotationalSemantics.Model.Monad

module MonomorphicCalculus.DenotationalSemantics.Interpretation.Data
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Bool.Base using (true; false) renaming (Bool to 𝔹)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)

open LanguageSpec S

open import Language.Comparisons
open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Terms S
  using (_⊢ᵛ⦂_; cmp; const; ⋆; true; false; zero; succ; ⦉_,_⦊; inl; inr; nil; cons)
open import MonomorphicCalculus.Syntax.Data      S

open Category Cat
open GroundTypes GTy

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types       S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Comparisons S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms       S Cat Fut Pst Adj GTy Mon GE

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- The embedded data are parametric

param-⌈⌉ : ∀ {Γ A} → (et : Et A) → (d : ⟪ A ⟫) → Paramᵛ {Γ} (⌈ et ⌉ d)
param-⌈⌉ (Baseₑ _)      _        = tt
param-⌈⌉ unitₑ          _        = tt
param-⌈⌉ boolₑ          true     = tt
param-⌈⌉ boolₑ          false    = tt
param-⌈⌉ natₑ           zero     = tt
param-⌈⌉ natₑ           (suc n)  = param-⌈⌉ natₑ n
param-⌈⌉ (et₁ |×|ₑ et₂) (x , y)  = param-⌈⌉ et₁ x , param-⌈⌉ et₂ y
param-⌈⌉ (et₁ |+|ₑ et₂) (inj₁ x) = param-⌈⌉ et₁ x
param-⌈⌉ (et₁ |+|ₑ et₂) (inj₂ y) = param-⌈⌉ et₂ y
param-⌈⌉ (listₑ et)     []       = tt
param-⌈⌉ (listₑ et)     (x ∷ xs) = param-⌈⌉ et x , param-⌈⌉ (listₑ et) xs
param-⌈⌉ emptyₑ         ()

-- An embedded datum denotes its point

⟦⌈⌉⟧ : ∀ {Γ A} → (et : Et A) → (d : ⟪ A ⟫)
     → ⟦ ⌈_⌉ {Γ} et d ⟧ᵛᵗ (param-⌈⌉ et d) ≈ᵐ ⌜ et ⌝ᵈ d ∘ᵐ terminalᵐ
⟦⌈⌉⟧ (Baseₑ _)      _        = ≈ᵐ-refl
⟦⌈⌉⟧ unitₑ          _        = ≈ᵐ-sym terminalᵐ-unique
⟦⌈⌉⟧ boolₑ          true     = ≈ᵐ-refl
⟦⌈⌉⟧ boolₑ          false    = ≈ᵐ-refl
⟦⌈⌉⟧ natₑ           zero     = ≈ᵐ-refl
⟦⌈⌉⟧ natₑ           (suc n)  = ∘ᵐ-congʳ (⟦⌈⌉⟧ natₑ n) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⟦⌈⌉⟧ (et₁ |×|ₑ et₂) (x , y)  =
  ⟨ ⟦⌈⌉⟧ et₁ x , ⟦⌈⌉⟧ et₂ y ⟩ᵐ-cong ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)
⟦⌈⌉⟧ (et₁ |+|ₑ et₂) (inj₁ x) = ∘ᵐ-congʳ (⟦⌈⌉⟧ et₁ x) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⟦⌈⌉⟧ (et₁ |+|ₑ et₂) (inj₂ y) = ∘ᵐ-congʳ (⟦⌈⌉⟧ et₂ y) ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⟦⌈⌉⟧ (listₑ et)     []       = ≈ᵐ-refl
⟦⌈⌉⟧ (listₑ et)     (x ∷ xs) =
    ∘ᵐ-congʳ (⟨ ⟦⌈⌉⟧ et x , ⟦⌈⌉⟧ (listₑ et) xs ⟩ᵐ-cong ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
⟦⌈⌉⟧ emptyₑ         ()

-- A comparison of values denoting data's points denotes the boolean constant
-- of the relation's truth on the data's order.

sound-cmp : ∀ {Γ A} → (⋈ : Cmp) → (et : Et A) → (V W : Γ ⊢ᵛ⦂ A)
          → (pV : Paramᵛ V) → (pW : Paramᵛ W) → (d e : ⟪ A ⟫)
          → ⟦ V ⟧ᵛᵗ pV ≈ᵐ ⌜ et ⌝ᵈ d ∘ᵐ terminalᵐ
          → ⟦ W ⟧ᵛᵗ pW ≈ᵐ ⌜ et ⌝ᵈ e ∘ᵐ terminalᵐ
          → ⟦ cmp ⋈ V W et ⟧ᵛᵗ (pV , pW)
            ≈ᵐ ⟦ ⌈_⌉ᵇ {Γ} (holds ⋈ (compareᵈ et d e)) ⟧ᵛᵗ
                 (param-⌈⌉ boolₑ (holds ⋈ (compareᵈ et d e)))
sound-cmp ⋈ et V W pV pW d e eV eW =
    ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ eV , eW ⟩ᵐ-cong ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (cmpᵐ-pt et d e))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (holdsᵐ-pt ⋈ (compareᵈ et d e))
  ∙ ≈ᵐ-sym (⟦⌈⌉⟧ boolₑ (holds ⋈ (compareᵈ et d e)))
