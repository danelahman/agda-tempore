------------------------------------------------------------------------
-- Soundness of the modal commutation equations.                      --
-- `unbox-comm`/`box-comm`/`box-unbox-comm` say two independent       --
-- resource binders commute; `comm-l`/`comm-r` normalise both orders  --
-- to the same composite.                                             --
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

module MonomorphicCalculus.EquationalTheory.Soundness.Comm
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

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename)
open import MonomorphicCalculus.Syntax.Substitution    S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; η⊣-nat; ε⊣)
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

-- The two nestings of environment extensions, each normalised.

comm-l : ∀ {Γ₀ A B Z} → (m : (Γ₀ ×ᵐ A) ×ᵐ B →ᵐ Z)
       → (a : Γ₀ →ᵐ A) → (b : Γ₀ →ᵐ B)
       → (m ∘ᵐ ⟨ idᵐ , b ∘ᵐ fstᵐ ⟩ᵐ) ∘ᵐ ⟨ idᵐ , a ⟩ᵐ
       ≈ᵐ m ∘ᵐ ⟨ ⟨ idᵐ , a ⟩ᵐ , b ⟩ᵐ
comm-l m a b =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-identityˡ _
                ,   ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                  ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)

comm-r : ∀ {Γ₀ A B Z} → (m : (Γ₀ ×ᵐ A) ×ᵐ B →ᵐ Z)
       → (a : Γ₀ →ᵐ A) → (b : Γ₀ →ᵐ B)
       → ((m ∘ᵐ ⟨ mapˣᵐ fstᵐ idᵐ , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ) ∘ᵐ ⟨ idᵐ , a ∘ᵐ fstᵐ ⟩ᵐ)
           ∘ᵐ ⟨ idᵐ , b ⟩ᵐ
       ≈ᵐ m ∘ᵐ ⟨ ⟨ idᵐ , a ⟩ᵐ , b ⟩ᵐ
comm-r m a b =
    ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                          ∙ ⟨ ∘ᵐ-identityˡ _
                            ,   ∘ᵐ-assoc _ _ _
                              ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                              ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)
              ∙ ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨   mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                ,   ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                  ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)

-- A boxed value weakened past an intervening binder: the weakening slides out
-- of the box by `η⊣`-naturality.

box-wk : ∀ {Γ B ρ'} → (X : VType) → (W : Γ ⟨ ρ' ⟩ ⊢V⦂ B) → (pW : Paramᵛ W)
       → [ ρ' ]ᶠ (⟦ V-rename (cong-⟨⟩-ren (wk-ren {A = X})) W ⟧ᵛᵗ
                    (renᵛ (cong-⟨⟩-ren (wk-ren {A = X})) W pW)) ∘ᵐ η⊣
       ≈ᵐ ([ ρ' ]ᶠ (⟦ W ⟧ᵛᵗ pW) ∘ᵐ η⊣) ∘ᵐ fstᵐ
box-wk X W pW =
    ∘ᵐ-congˡ (  []-congᶠ (V-rename-nat (cong-⟨⟩-ren (wk-ren {A = X})) W pW)
              ∙ []-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (η⊣-nat fstᵐ)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

sound-unbox-comm : ∀ {Γ A A₁ B B₂ C ρ₁ ρ₁' ρ₂ ρ₂'}
                 → (x₁ : [ ρ₁ ] A₁ ∈[ ρ₁' ] Γ) → (rel₁ : ρ₁' ≾ᵣ ρ₁)
                 → (w₁ : A₁ <:ᵛ A)
                 → (x₂ : [ ρ₂ ] B₂ ∈[ ρ₂' ] Γ) → (rel₂ : ρ₂' ≾ᵣ ρ₂)
                 → (w₂ : B₂ <:ᵛ B)
                 → (M : Γ ∷ A ∷ B ⊢C⦂ C)
                 → Soundᶜ≡ᵗʰ (unbox-comm x₁ rel₁ w₁ x₂ rel₂ w₂ M)
sound-unbox-comm {Γ = Γ} {A = A} {B = B} x₁ rel₁ w₁ x₂ rel₂ w₂ M pM pR =
    unbox-def x₁ rel₁ w₁ (unbox (Tl-∷ x₂) rel₂ w₂ M) pM
  ∙ ∘ᵐ-congˡ (unbox-def (Tl-∷ x₂) rel₂ w₂ M pM)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                        ,   ∘ᵐ-congʳ (unbox-env-nat (wk-ren {A = A}) x₂ rel₂ rel₂)
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong))
  ∙ comm-l (⟦ M ⟧ᶜᵗ pM) _ _
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox x₂ rel₂ w₂
                         (unbox (Tl-∷ x₁) rel₁ w₁ (C-rename exch-ren M)))
                pR (renᶜ exch-ren M pM)
            ∙ unbox-def x₂ rel₂ w₂
                (unbox (Tl-∷ x₁) rel₁ w₁ (C-rename exch-ren M))
                (renᶜ exch-ren M pM)
            ∙ ∘ᵐ-congˡ (unbox-def (Tl-∷ x₁) rel₁ w₁ (C-rename exch-ren M)
                          (renᶜ exch-ren M pM))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (  C-rename-nat exch-ren M pM
                                  ∙ ∘ᵐ-congʳ (exch-ren-mor {Γ} {B} {A})))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                                  ,   ∘ᵐ-congʳ (unbox-env-nat (wk-ren {A = B}) x₁ rel₁ rel₁)
                                    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong))
            ∙ comm-r (⟦ M ⟧ᶜᵗ pM) _ _)

sound-box-comm : ∀ {Γ A B C ρ ρ'}
               → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (W : Γ ⟨ ρ' ⟩ ⊢V⦂ B)
               → (M : Γ ∷ [ ρ ] A ∷ [ ρ' ] B ⊢C⦂ C)
               → Soundᶜ≡ᵗʰ (box-comm V W M)
sound-box-comm {Γ = Γ} {A = A} {B = B} {ρ = ρ} {ρ' = ρ'} V W M (pV , (pW' , pM)) (pW , (pV' , pMr)) =
    ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                        ,   ∘ᵐ-congˡ ([]-congᶠ
                              (⟦⟧ᵛᵗ-irr (V-rename (cong-⟨⟩-ren wk-ren) W) pW'
                                 (renᵛ (cong-⟨⟩-ren wk-ren) W pW)))
                          ∙ box-wk ([ ρ ] A) W pW ⟩ᵐ-cong))
  ∙ comm-l (⟦ M ⟧ᶜᵗ pM) _ _
  ∙ ≈ᵐ-sym (  ∘ᵐ-congˡ (∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (C-rename exch-ren M) pMr
                                      (renᶜ exch-ren M pM)
                                  ∙ C-rename-nat exch-ren M pM
                                  ∙ ∘ᵐ-congʳ (exch-ren-mor {Γ} {[ ρ' ] B} {[ ρ ] A})))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                                  ,   ∘ᵐ-congˡ ([]-congᶠ
                                        (⟦⟧ᵛᵗ-irr (V-rename (cong-⟨⟩-ren wk-ren) V) pV'
                                           (renᵛ (cong-⟨⟩-ren wk-ren) V pV)))
                                    ∙ box-wk ([ ρ' ] B) V pV ⟩ᵐ-cong))
            ∙ comm-r (⟦ M ⟧ᶜᵗ pM) _ _)

sound-box-unbox-comm : ∀ {Γ A B B₂ C ρ ρ₂ ρ₂'}
                     → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                     → (x₂ : [ ρ₂ ] B₂ ∈[ ρ₂' ] Γ) → (rel₂ : ρ₂' ≾ᵣ ρ₂)
                     → (w₂ : B₂ <:ᵛ B)
                     → (M : Γ ∷ [ ρ ] A ∷ B ⊢C⦂ C)
                     → Soundᶜ≡ᵗʰ (box-unbox-comm V x₂ rel₂ w₂ M)
sound-box-unbox-comm {Γ = Γ} {A = A} {B = B} {ρ = ρ} V x₂ rel₂ w₂ M (pV , pM) pR =
    ∘ᵐ-congˡ (  unbox-def (Tl-∷ x₂) rel₂ w₂ M pM
              ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                          ,   ∘ᵐ-congʳ (unbox-env-nat (wk-ren {A = [ ρ ] A}) x₂ rel₂ rel₂)
                            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong))
  ∙ comm-l (⟦ M ⟧ᶜᵗ pM) _ _
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox x₂ rel₂ w₂ (box _ (V-rename (cong-⟨⟩-ren wk-ren) V)
                                              (C-rename exch-ren M)))
                pR (renᵛ (cong-⟨⟩-ren wk-ren) V pV , renᶜ exch-ren M pM)
            ∙ unbox-def x₂ rel₂ w₂ (box _ (V-rename (cong-⟨⟩-ren wk-ren) V)
                                        (C-rename exch-ren M))
                (renᵛ (cong-⟨⟩-ren wk-ren) V pV , renᶜ exch-ren M pM)
            ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (  C-rename-nat exch-ren M pM
                                  ∙ ∘ᵐ-congʳ (exch-ren-mor {Γ} {B} {[ ρ ] A})))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , box-wk B V pV ⟩ᵐ-cong))
            ∙ comm-r (⟦ M ⟧ᶜᵗ pM) _ _)
