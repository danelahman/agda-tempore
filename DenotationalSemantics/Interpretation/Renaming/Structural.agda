------------------------------------------------------------------------
-- Denotations of the structural renamings.
------------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad
module DenotationalSemantics.Interpretation.Renaming.Structural
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


open import Syntax.Types      S
open import Syntax.Contexts   S
open import Syntax.Renamings  S
open import Syntax.RenActions S using (var-rename)
open import Syntax.Renamings.Equivalence S using (eternal?-yes)

open Category Cat
open Past Pst
open GroundEternal GE
open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming.Algebra S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming.Extension S Cat Fut Pst Adj GTy Mon GE

-- ───────────────────────────────────────────────────────────────────────────
-- DENOTATIONS OF THE STRUCTURAL RENAMINGS
--
-- `exch-ren` (swap the two topmost variables), `bring-up` (extrude an eternal
-- variable out from under a suffix) and `contract` (fold the eternal prefix
-- `Γ ᴱ` back into `Γ`'s own variables).
-- ───────────────────────────────────────────────────────────────────────────

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
    ∘ᵐ-congʳ (  exch-ren-mor {Δ ++ᶜ Θ} {B} {A}
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

-- The denotation of the eternal inclusion `ᴱ-ren Γ : Ren [] Γ` (Γ ᴱ) is the
-- eternal projection: the two are defined by the same `eternal?` recursion, the
-- lock case matching `extᵉ` against `⟨⟩-ext-ctx`. That case needs the two
-- eternal structures on `⟦ Γ ᴱ ⟧` — the one read off the `EternalCtx` witness
-- and the one `projᴱ` uses — to agree, which they do, by the same recursion.

ec-Eternalᵒ-ᴱ : (Γ : Ctx) → ec-Eternalᵒ (ᴱ-EternalCtx Γ) ≡ ⟦ Γ ⟧ᴱ-Eternalᵒ
ec-Eternalᵒ-ᴱ []        = refl
ec-Eternalᵒ-ᴱ (Γ ∷ A)   with eternal? A
... | yes et = cong (λ z → ×-eternalᵒ z (eternalᵛ-Eternalᵒ et)) (ec-Eternalᵒ-ᴱ Γ)
... | no  _  = ec-Eternalᵒ-ᴱ Γ
ec-Eternalᵒ-ᴱ (Γ ⟨ ρ ⟩) = ec-Eternalᵒ-ᴱ Γ

ᴱ-ren-mor : (Γ : Ctx) → ⟦ ᴱ-ren Γ ⟧ʳ ≈ᵐ projᴱ Γ
ᴱ-ren-mor []        = ≈ᵐ-refl
ᴱ-ren-mor (Γ ∷ A)   with eternal? A
... | yes _ = mapˣᵐ-cong (ᴱ-ren-mor Γ) ≈ᵐ-refl
... | no  _ = ∘ᵐ-congˡ (ᴱ-ren-mor Γ)
ᴱ-ren-mor (Γ ⟨ ρ ⟩) =
    ∘ᵐ-cong (≡→≈ᵐ (cong (λ eΓ → Eternalᵒ.extᵉ eΓ {ρ}) (ec-Eternalᵒ-ᴱ Γ)))
            (⟨⟩-congᶠ (ᴱ-ren-mor Γ))

-- The denotation of the eternal-prefix contraction `contract Γ : Ren (Γ ++ᶜ ᴱ Γ) Γ`:
-- pair the identity with `projᴱ Γ`, then `splitᴱ⁻¹` glues the eternal base back on.

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
-- an eternal head grows the base `Γ ᴱ → Γ ᴱ ∷ A`, which `bring-up-mor` carries
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
