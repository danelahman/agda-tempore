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
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open GroundEternal GE using (×-eternalᵒ)
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
       using (exch-ren-mor)

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
-- TODO: same shape; `⟦⟨⟩-ext-ren et⟧`=`strᵉ`, `splitᴰ`'s ⟨⟩ case = `costrᵉ`.
bring-up-mor eA eΔ (Θ ⟨ ρ ⟩) = {!!}

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
... | yes eA = {!!}
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
