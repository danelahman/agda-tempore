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
-- `exch-ren` (swap the two topmost variables) and `ᴱ-ren` (project a context
-- onto its eternal prefix `Γ ᴱ`).
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