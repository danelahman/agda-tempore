------------------------------------------------------------------------
-- Soundness of the `handle-perform` equation (the last axiom).          --
--                                                                      --
-- Development module (not yet in Everything.agda). General renaming     --
-- lemmas proved here (`contract-mor`) will move to their proper homes    --
-- once the whole axiom is green.                                        --
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

module EquationalTheory.Soundness.HandlePerform
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open import Data.Product using (_,_; _×_; Σ; Σ-syntax; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_; yes; no)

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename; unbox⇒var; var-rename)
open import Syntax.Substitutions S

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ; μ)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open GroundEternal GE using (×-eternalᵒ; ×-eternalᵒ-extᵉ)
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import EquationalTheory.Soundness.Values S Cat Fut Pst Adj GTy Mon GE
       using (exch-ren-mor; var-morphism-Hd)

open import DenotationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE
       using (box-split; η⊣-⟨⟩)
open import DenotationalSemantics.Soundness.Preservation.Handle S Cat Fut Pst Adj GTy Mon GE
       using (op-pair; op-env)

infixr 3 _∙_
_∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
_∙_ = ≈ᵐ-trans

-- denotation of `bring-up`: split the extension off the eternal base, keep the
-- head `A`, and re-glue with `A` adjoined to the base.
bring-up-mor : ∀ {Δ A} → (eA : Eternal A) → (eΔ : Eternalᵒ ⟦ Δ ⟧ᶜᵗˣ) → (Θ : Ctx)
  → ⟦ bring-up {Δ} {A} eA Θ ⟧ʳ
  ≈ᵐ splitᴰ⁻¹ (Δ ∷ A) (×-eternalᵒ eΔ (eternalᵛ-Eternalᵒ eA)) Θ
      ∘ᵐ ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ
         , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
bring-up-mor eA eΔ [] =
    ≈ᵐ-sym (
        ⟨⟩ᵐ-sndᵐ _ _
      ∙ ⟨   ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _) ∙ ∘ᵐ-identityˡ _
          , ≈ᵐ-refl ⟩ᵐ-cong
      ∙ ≈ᵐ-sym (⟨⟩ᵐ-unique fstᵐ sndᵐ idᵐ (∘ᵐ-identityʳ _) (∘ᵐ-identityʳ _)))
bring-up-mor {Δ} {A} eA eΔ (Θ ∷ B) =
    ∘ᵐ-congʳ (  exch-ren-mor {Δ ++ᶜ Θ} {A} {B}
              ∙ ⟨ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congˡ (mapˣᵐ-cong (bring-up-mor eA eΔ Θ) ≈ᵐ-refl)
  ∙ ∘ᵐ-congˡ (  mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym (∘ᵐ-identityˡ idᵐ))
              ∙ ≈ᵐ-sym (mapˣᵐ-∘ T idᵐ Pθ idᵐ))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ swapP
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    sd = splitᴰ Δ eΔ Θ
    T  = splitᴰ⁻¹ (Δ ∷ A) (×-eternalᵒ eΔ (eternalᵛ-Eternalᵒ eA)) Θ
    Pθ = ⟨ fstᵐ ∘ᵐ sd ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ sd ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    -- the two components of `splitᴰ Δ eΔ (Θ ∷ B)` = `swap₂₃ ∘ᵐ mapˣᵐ S idᵐ`
    sB-fst : fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ≈ᵐ ⟨ fstᵐ ∘ᵐ sd ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ
    sB-fst =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
          , ⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-identityˡ _ ⟩ᵐ-cong
    sB-snd : sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ≈ᵐ sndᵐ ∘ᵐ sd ∘ᵐ fstᵐ
    sB-snd =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
    PΘB = ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ∘ᵐ fstᵐ
          , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ∷ B) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    -- LHS → common form C = ⟨ ⟨ fstᵐ∘sd∘(fstᵐ∘fstᵐ) , ⟨ sndᵐ∘sd∘(fstᵐ∘fstᵐ) , sndᵐ ⟩ ⟩ , sndᵐ∘fstᵐ ⟩
    swapP-lhs : mapˣᵐ Pθ idᵐ ∘ᵐ swap₂₃
              ≈ᵐ ⟨ ⟨ fstᵐ ∘ᵐ sd ∘ᵐ fstᵐ ∘ᵐ fstᵐ
                   , ⟨ sndᵐ ∘ᵐ sd ∘ᵐ fstᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
                 , sndᵐ ∘ᵐ fstᵐ ⟩ᵐ
    swapP-lhs =
        mapˣᵐ-∘⟨⟩ _ _ _ _
      ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
              , ⟨⟩ᵐ-∘ _ _ _
                ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _))
                    , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong ⟩ᵐ-cong
        , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
    swapP : mapˣᵐ Pθ idᵐ ∘ᵐ swap₂₃ ≈ᵐ swap₂₃ ∘ᵐ PΘB
    swapP = swapP-lhs ∙ ≈ᵐ-sym
      (  ⟨⟩ᵐ-∘ _ _ _
       ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
           ∙ ⟨   -- (fstᵐ ∘ᵐ fstᵐ) ∘ᵐ PΘB → fstᵐ ∘ᵐ sd ∘ᵐ (fstᵐ ∘ᵐ fstᵐ)
                 ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
               ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ sB-fst)
               ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
               ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
               -- sndᵐ ∘ᵐ PΘB → ⟨ sndᵐ ∘ᵐ sd ∘ᵐ (fstᵐ ∘ᵐ fstᵐ) , sndᵐ ⟩
             , ⟨⟩ᵐ-sndᵐ _ _
               ∙ ⟨   ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ sB-snd
                   ∙ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                 , ≈ᵐ-refl ⟩ᵐ-cong ⟩ᵐ-cong
           -- (sndᵐ ∘ᵐ fstᵐ) ∘ᵐ PΘB → sndᵐ ∘ᵐ fstᵐ
         , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
           ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ sB-fst)
           ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _) ⟩ᵐ-cong)
bring-up-mor {Δ} {A} eA eΔ (Θ ⟨ ρ ⟩) =
    ∘ᵐ-congˡ (⟨⟩-congᶠ (bring-up-mor eA eΔ Θ))
  ∙ ∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ strP
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    eA' = eternalᵛ-Eternalᵒ eA
    Pθ  = ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ
          , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    PρΘ = ⟨ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ
          , ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ
    refold1 : ⟨ ρ ⟩ᶠ (fstᵐ ∘ᵐ splitᴰ Δ eΔ Θ) ≈ᵐ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩)
    refold1 =
        ⟨⟩-∘ᵐ _ _
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-assoc _ _ _
    refold2 : Eternalᵒ.extᵉ eΔ ∘ᵐ ⟨ ρ ⟩ᶠ (sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ)
            ≈ᵐ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩)
    refold2 =
        ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩ᵐ-sndᵐ _ _))
      ∙ ∘ᵐ-assoc _ _ _
    comp1 : ⟨ ρ ⟩ᶠ fstᵐ ∘ᵐ (⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA')
          ≈ᵐ fstᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ
    comp1 =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _))
      ∙ ∘ᵐ-congˡ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (Eternalᵒ.strᵉ-fstᵐ eA')
      ∙ ∘ᵐ-congˡ refold1
      ∙ ∘ᵐ-assoc _ _ _
    c2a : (Eternalᵒ.extᵉ eΔ ∘ᵐ ⟨ ρ ⟩ᶠ fstᵐ)
            ∘ᵐ (⟨ ρ ⟩ᶠ ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ∘ᵐ Eternalᵒ.strᵉ eA')
        ≈ᵐ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ
    c2a =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-∘ᵐ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (Eternalᵒ.strᵉ-fstᵐ eA'))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ refold2
      ∙ ∘ᵐ-assoc _ _ _
    c2b : (Eternalᵒ.extᵉ eA' ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ)
            ∘ᵐ (⟨ ρ ⟩ᶠ ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ Θ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ∘ᵐ Eternalᵒ.strᵉ eA')
        ≈ᵐ sndᵐ
    c2b =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
      ∙ Eternalᵒ.strᵉ-sndᵐ eA'
    comp2 : (Eternalᵒ.extᵉ (×-eternalᵒ eΔ eA') ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ)
              ∘ᵐ (⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA')
          ≈ᵐ ⟨ sndᵐ ∘ᵐ splitᴰ Δ eΔ (Θ ⟨ ρ ⟩) ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ
    comp2 =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)))
      ∙ ∘ᵐ-congˡ (×-eternalᵒ-extᵉ eΔ eA')
      ∙ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ c2a , c2b ⟩ᵐ-cong
    costrP : Eternalᵒ.costrᵉ (×-eternalᵒ eΔ eA') ∘ᵐ (⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA')
           ≈ᵐ PρΘ
    costrP = ⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ comp1 , comp2 ⟩ᵐ-cong
    strP : ⟨ ρ ⟩ᶠ Pθ ∘ᵐ Eternalᵒ.strᵉ eA'
         ≈ᵐ Eternalᵒ.strᵉ (×-eternalᵒ eΔ eA') ∘ᵐ PρΘ
    strP =
        ≈ᵐ-sym (∘ᵐ-identityˡ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.costrᵉ-strᵉ (×-eternalᵒ eΔ eA')))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ costrP

-- ═══════════════════════════════════════════════════════════════════════════
-- BRICK 1: the denotation of the eternal-prefix contraction.
-- `contract Γ : Ren (Γ ᴱ ++ᶜ Γ) Γ` re-assembles `Γ` together with its eternal
-- projection: pair the identity with `projᴱ Γ`, then `splitᴱ⁻¹` glues on the base.
-- ═══════════════════════════════════════════════════════════════════════════

-- the pure-cartesian reshuffle used in the non-eternal `∷` case
private
  cart-∷ : ∀ {Y B C} → (p : Y →ᵐ B)
         → mapˣᵐ ⟨ idᵐ , p ⟩ᵐ (idᵐ {C}) ≈ᵐ swap₂₃ ∘ᵐ ⟨ idᵐ , p ∘ᵐ fstᵐ ⟩ᵐ
  cart-∷ p =
      ⟨ ⟨⟩ᵐ-∘ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
    ∙ ≈ᵐ-sym
        (  ⟨⟩ᵐ-∘ _ _ _
         ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
             ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _
               , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
           , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)

contract-mor : (Γ : Ctx) → ⟦ contract Γ ⟧ʳ ≈ᵐ splitᴱ⁻¹ Γ Γ ∘ᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ
contract-mor []        = ≈ᵐ-sym (⟨⟩ᵐ-sndᵐ idᵐ idᵐ)
contract-mor (Γ ∷ A) with eternal? A
-- TODO: the eternal head grows the base `Γ ᴱ → Γ ᴱ ∷ A`; needs a `bring-up`
-- denotation lemma (induction through `exch-ren` = `exch-ren-mor` and
-- `⟨⟩-ext-ren` = `strᵉ`) relating `splitᴰ⁻¹ (Γ ᴱ ∷ A) _ Γ` to `splitᴱ⁻¹ Γ Γ`.
... | yes eA =
    ∘ᵐ-congˡ (  ∘ᵐ-congˡ (mapˣᵐ-cong (bring-up-mor {Γ ᴱ} {A} eA (⟦ Γ ⟧ᴱ-Eternalᵒ) Γ) ≈ᵐ-refl)
              ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , var-morphism-Hd {Γ ᴱ ++ᶜ Γ} {A} _ ⟩ᵐ-cong))
  ∙ ∘ᵐ-congʳ (mapˣᵐ-cong (contract-mor Γ) ≈ᵐ-refl)
  ∙ rem-eternal
  where
    e' = ×-eternalᵒ (⟦ Γ ⟧ᴱ-Eternalᵒ) (eternalᵛ-Eternalᵒ eA)
    T' = splitᴰ⁻¹ (Γ ᴱ ∷ A) e' Γ
    sg = splitᴱ Γ Γ
    K  = splitᴱ⁻¹ Γ Γ ∘ᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ
    P  = mapˣᵐ (projᴱ Γ) (idᵐ {⟦ A ⟧ᵛ})
    mK = mapˣᵐ K (idᵐ {⟦ A ⟧ᵛ})
    Pγ = ⟨ fstᵐ ∘ᵐ sg ∘ᵐ fstᵐ , ⟨ sndᵐ ∘ᵐ sg ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ

    splitM : mapˣᵐ (T' ∘ᵐ Pγ) (idᵐ {⟦ A ⟧ᵛ})
           ≈ᵐ mapˣᵐ T' (idᵐ {⟦ A ⟧ᵛ}) ∘ᵐ mapˣᵐ Pγ (idᵐ {⟦ A ⟧ᵛ})
    splitM =
        mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym (∘ᵐ-identityˡ idᵐ))
      ∙ ≈ᵐ-sym (mapˣᵐ-∘ T' idᵐ Pγ idᵐ)

    -- the split/re-glue round trip collapses (`splitᴱ-iso`)
    sgK : sg ∘ᵐ K ≈ᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ
    sgK = ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (splitᴱ-iso Γ Γ) ∙ ∘ᵐ-identityˡ _

    fstK : fstᵐ ∘ᵐ mK ≈ᵐ K ∘ᵐ fstᵐ
    fstK = ⟨⟩ᵐ-fstᵐ _ _

    sndK : sndᵐ ∘ᵐ mK ≈ᵐ sndᵐ
    sndK = ⟨⟩ᵐ-sndᵐ _ _ ∙ ∘ᵐ-identityˡ _

    legA : (fstᵐ ∘ᵐ sg ∘ᵐ fstᵐ) ∘ᵐ mK ≈ᵐ fstᵐ
    legA =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ fstK)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ sgK)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
      ∙ ∘ᵐ-identityˡ _

    legB : (sndᵐ ∘ᵐ sg ∘ᵐ fstᵐ) ∘ᵐ mK ≈ᵐ projᴱ Γ ∘ᵐ fstᵐ
    legB =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ fstK)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ sgK)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)

    pgEq : Pγ ∘ᵐ mK ≈ᵐ ⟨ fstᵐ , P ⟩ᵐ
    pgEq =
        ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ legA
        ,   ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ legB , sndK ⟩ᵐ-cong
          ∙ ≈ᵐ-sym (⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong) ⟩ᵐ-cong

    wEq : (mapˣᵐ Pγ (idᵐ {⟦ A ⟧ᵛ}) ∘ᵐ ⟨ idᵐ , sndᵐ ⟩ᵐ) ∘ᵐ mK
        ≈ᵐ swap₂₃ ∘ᵐ ⟨ idᵐ , P ⟩ᵐ
    wEq =
        ∘ᵐ-congˡ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
      ∙ ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨ pgEq , sndK ⟩ᵐ-cong
      ∙ ≈ᵐ-sym
          (  ⟨⟩ᵐ-∘ _ _ _
           ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
               ∙ ⟨   ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _
                   , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong
             , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityʳ _ ⟩ᵐ-cong)

    rem-eternal =
        ∘ᵐ-congˡ (∘ᵐ-congˡ splitM)
      ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ wEq
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
... | no ¬eA =
    mapˣᵐ-cong (contract-mor Γ) ≈ᵐ-refl
  ∙ mapˣᵐ-cong ≈ᵐ-refl (≈ᵐ-sym (∘ᵐ-identityˡ idᵐ))
  ∙ ≈ᵐ-sym (mapˣᵐ-∘ (splitᴱ⁻¹ Γ Γ) idᵐ ⟨ idᵐ , projᴱ Γ ⟩ᵐ idᵐ)
  ∙ ∘ᵐ-congʳ (cart-∷ {C = ⟦ A ⟧ᵛ} (projᴱ Γ))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
contract-mor (Γ ⟨ ρ ⟩) =
    ⟨⟩-congᶠ (contract-mor Γ)
  ∙ ⟨⟩-∘ᵐ _ _
  ∙ ∘ᵐ-congʳ strident
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    e = ⟦ Γ ⟧ᴱ-Eternalᵒ
    q = projᴱ Γ
    costr-comp : Eternalᵒ.costrᵉ e {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ ⟨ idᵐ , q ⟩ᵐ
               ≈ᵐ ⟨ idᵐ , Eternalᵒ.extᵉ e ∘ᵐ ⟨ ρ ⟩ᶠ q ⟩ᵐ
    costr-comp =
        ⟨⟩ᵐ-∘ _ _ _
      ∙ ⟨   ≈ᵐ-sym (⟨⟩-∘ᵐ _ _) ∙ ⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _) ∙ ⟨⟩-idᵐ
          , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _) ∙ ⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)) ⟩ᵐ-cong
    strident : ⟨ ρ ⟩ᶠ ⟨ idᵐ , q ⟩ᵐ
             ≈ᵐ Eternalᵒ.strᵉ e {ρ} ∘ᵐ ⟨ idᵐ , Eternalᵒ.extᵉ e ∘ᵐ ⟨ ρ ⟩ᶠ q ⟩ᵐ
    strident =
        ≈ᵐ-sym (∘ᵐ-identityˡ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (Eternalᵒ.costrᵉ-strᵉ e))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ costr-comp


-- ═══════════════════════════════════════════════════════════════════════════
-- BRICK 2: pushing a sequel under an operation, WITHOUT an algebra.
--
-- `seq-op-box`/`seq-op-core` (Preservation/Handle) bake in a parameter-free
-- algebra `alg`, which a handler with a live eternal parameter is not. These
-- are the same two moves with that layer removed: what is left is exactly the
-- strength's own algebraicity, so the sequel `n` ends up inside the
-- operation's (boxed) continuation and nothing else changes.
-- ═══════════════════════════════════════════════════════════════════════════

str-op-box : ∀ {X A B ε ε'} → (op : Op)
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ n))
      ∘ᵐ ( [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (strᵀ {_} {A} {ε}) ∘ᵐ exp-strᵐ)
         ∘ᵐ []-monoidal
         ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ )
      ∘ᵐ ⟨ η⊣ {X} {mapᵉ (op-grade op ·ₑ ε)}
         , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ m) ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)} ⟩ᵐ
  ≈ᵐ [ mapᵉ (op-grade op) ]ᶠ
       (curryᵐ (Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ))
     ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)}
str-op-box {X} {A} {B} {ε} {ε'} op m n rn ern =
  -- bring the strength law's reshuffle up against the operation's arguments
    ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- split the environment's box, and pair the two transposed halves under one
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (  mapˣᵐ-∘⟨⟩ _ _ _ _
       ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ box-split _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _))
  -- collect everything under a single box
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  -- inside the box: push the environment under the exponential and collapse
  ∙ ∘ᵐ-congˡ ([]-congᶠ
      (  ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (exp-strᵐ-⟨⟩ _ _))
       ∙ ∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _)
       ∙ map⇒ᵐ-curryᵐ _ _))
  -- and recognise the syntax's renaming as the environment `n` receives
  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (≈ᵐ-sym
      (  ∘ᵐ-congˡ (T-∘ᵐ n (mapˣᵐ rn idᵐ))
       ∙ ∘ᵐ-assoc _ _ _
       ∙ body))))
  where
    body : Tᶠ n ∘ᵐ Tᶠ (mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
         ≈ᵐ Tᶠ n ∘ᵐ strᵀ
              ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣)
                     ∘ᵐ fstᵐ
                 , m ⟩ᵐ
    body =
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ rn))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-congˡ ([]-congᶠ ern) ∙ ≈ᵐ-sym (op-env _) , ≈ᵐ-refl ⟩ᵐ-cong))

str-op : ∀ {X Y A B ε ε'} → (op : Op)
  → (ea : Y ≡ ⟦ arity op ⟧ᵍ)
  → (v : X →ᵐ ⟦ param op ⟧ᵍ)
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → Tᶠ n ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣
         , opᵀ op
             ∘ᵐ ⟨ v
                , [ mapᵉ (op-grade op) ]ᶠ
                    (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                          →ᵐ Tᵒ A ε)
                                   ea m))
                    ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≈ᵐ opᵀ op
     ∘ᵐ ⟨ v
        , [ mapᵉ (op-grade op) ]ᶠ
            (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                  →ᵐ Tᵒ (Tᵒ B ε') ε)
                           ea
                           (Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)))
          ∘ᵐ η⊣ ⟩ᵐ
str-op op refl v m n rn ern =
  -- the operation is a map on the strength's monadic component …
    ∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
  -- … so the strength pushes into it, carrying the environment under its box
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- the reshuffle hands the parameter back and pairs environment with cont.
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ op-pair _ _ _ _))
  -- the sequel is natural, so it too goes into the continuation
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op n))
  ∙ ∘ᵐ-assoc _ _ _
  -- collect the map on the continuation, and fire the box lemma
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , str-op-box op m n rn ern ⟩ᵐ-cong)
