------------------------------------------------------------------------
-- Soundness of the modal commutation equations.                        --
--                                                                    --
-- `unbox-comm`, `box-comm` and `box-unbox-comm` all say the same thing: --
-- two *independent* resource binders may be taken in either order, the   --
-- body being re-indexed by `exch-ren`. Denotationally each binder is an  --
-- environment extension `⟨ idᵐ , _ ⟩ᵐ` — a lookup `lk` for `unbox`, a    --
-- transposed box for `box` — and the equation is that the two extensions --
-- commute. Both orders normalise to `⟦M⟧ ∘ᵐ ⟨ ⟨ idᵐ , a ⟩ᵐ , b ⟩ᵐ`,      --
-- which is `comm-l` / `comm-r`; everything else is unfolding.           --
--                                                                    --
-- The inner binder's value/renaming is weakened past the outer one, so   --
-- each case first pushes that weakening out: `unbox⇒var-nat` for a       --
-- lookup, `box-wk` (below) for a box.                                    --
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

module EquationalTheory.Soundness.Comm
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

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (V-rename; C-rename; unbox⇒var)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-≤)
open Adjunction Adj using (η⊣; η⊣-nat; ε⊣)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Values S Cat Fut Pst Adj GTy Mon GE
       using (exch-ren-mor)

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

sound-unbox-comm : ∀ {Γ A B C ρ₁ Δ₁ ρ₂ Δ₂}
                 → (w₁ : Ren (Δ₁ ⟨ ρ₁ ⟩) Γ) → (V₁ : Δ₁ ⊢V⦂ [ ρ₁ ] A)
                 → (w₂ : Ren (Δ₂ ⟨ ρ₂ ⟩) Γ) → (V₂ : Δ₂ ⊢V⦂ [ ρ₂ ] B)
                 → (M : Γ ∷ A ∷ B ⊢C⦂ C)
                 → Soundᶜ== (unbox-comm w₁ V₁ w₂ V₂ M)
sound-unbox-comm {Γ = Γ} {A = A} {B = B} w₁ V₁ w₂ V₂ M (pV₁ , (pV₂ , pM)) pR =
    -- LHS: unfold both unboxings, push the inner lookup's weakening out
    unbox-def w₁ V₁ (unbox (wk-ren ∘ʳ w₂) V₂ M) pV₁ (pV₂ , pM)
  ∙ ∘ᵐ-congˡ (unbox-def (wk-ren ∘ʳ w₂) V₂ M pV₂ pM)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                        , unbox⇒var-nat (wk-ren {A = A}) w₂ V₂ ⟩ᵐ-cong))
  ∙ comm-l (⟦ M ⟧ᶜᵗ pM) _ _
    -- RHS: the same, with the exchange renaming unfolded
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox w₂ V₂ (unbox (wk-ren ∘ʳ w₁) V₁ (C-rename exch-ren M)))
                pR (pV₂ , (pV₁ , renᶜ exch-ren M pM))
            ∙ unbox-def w₂ V₂ (unbox (wk-ren ∘ʳ w₁) V₁ (C-rename exch-ren M))
                pV₂ (pV₁ , renᶜ exch-ren M pM)
            ∙ ∘ᵐ-congˡ (unbox-def (wk-ren ∘ʳ w₁) V₁ (C-rename exch-ren M)
                          pV₁ (renᶜ exch-ren M pM))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (  C-rename-nat exch-ren M pM
                                  ∙ ∘ᵐ-congʳ (exch-ren-mor {Γ} {A} {B})))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                                  , unbox⇒var-nat (wk-ren {A = B}) w₁ V₁ ⟩ᵐ-cong))
            ∙ comm-r (⟦ M ⟧ᶜᵗ pM) _ _)

sound-box-comm : ∀ {Γ A B C ρ ρ'}
               → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A) → (W : Γ ⟨ ρ' ⟩ ⊢V⦂ B)
               → (M : Γ ∷ [ ρ ] A ∷ [ ρ' ] B ⊢C⦂ C)
               → Soundᶜ== (box-comm V W M)
sound-box-comm {Γ = Γ} {A = A} {B = B} {ρ = ρ} {ρ' = ρ'} V W M (pV , (pW' , pM)) (pW , (pV' , pMr)) =
    -- LHS: the inner box's value is `W` weakened
    ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                        ,   ∘ᵐ-congˡ ([]-congᶠ
                              (⟦⟧ᵛᵗ-irr (V-rename (cong-⟨⟩-ren wk-ren) W) pW'
                                 (renᵛ (cong-⟨⟩-ren wk-ren) W pW)))
                          ∙ box-wk ([ ρ ] A) W pW ⟩ᵐ-cong))
  ∙ comm-l (⟦ M ⟧ᶜᵗ pM) _ _
    -- RHS: symmetrically, with the exchange renaming
  ∙ ≈ᵐ-sym (  ∘ᵐ-congˡ (∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (C-rename exch-ren M) pMr
                                      (renᶜ exch-ren M pM)
                                  ∙ C-rename-nat exch-ren M pM
                                  ∙ ∘ᵐ-congʳ (exch-ren-mor {Γ} {[ ρ ] A} {[ ρ' ] B})))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                                  ,   ∘ᵐ-congˡ ([]-congᶠ
                                        (⟦⟧ᵛᵗ-irr (V-rename (cong-⟨⟩-ren wk-ren) V) pV'
                                           (renᵛ (cong-⟨⟩-ren wk-ren) V pV)))
                                    ∙ box-wk ([ ρ' ] B) V pV ⟩ᵐ-cong))
            ∙ comm-r (⟦ M ⟧ᶜᵗ pM) _ _)

sound-box-unbox-comm : ∀ {Γ A B C ρ ρ₂ Δ₂}
                     → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                     → (w₂ : Ren (Δ₂ ⟨ ρ₂ ⟩) Γ) → (V₂ : Δ₂ ⊢V⦂ [ ρ₂ ] B)
                     → (M : Γ ∷ [ ρ ] A ∷ B ⊢C⦂ C)
                     → Soundᶜ== (box-unbox-comm V w₂ V₂ M)
sound-box-unbox-comm {Γ = Γ} {A = A} {B = B} {ρ = ρ} V w₂ V₂ M (pV , (pV₂ , pM)) pR =
    -- LHS: `box` outside, the inner lookup weakened past it
    ∘ᵐ-congˡ (  unbox-def (wk-ren ∘ʳ w₂) V₂ M pV₂ pM
              ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                          , unbox⇒var-nat (wk-ren {A = [ ρ ] A}) w₂ V₂ ⟩ᵐ-cong))
  ∙ comm-l (⟦ M ⟧ᶜᵗ pM) _ _
    -- RHS: `unbox` outside, the box weakened past it
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox w₂ V₂ (box (V-rename (cong-⟨⟩-ren wk-ren) V)
                                         (C-rename exch-ren M)))
                pR (pV₂ , (renᵛ (cong-⟨⟩-ren wk-ren) V pV , renᶜ exch-ren M pM))
            ∙ unbox-def w₂ V₂ (box (V-rename (cong-⟨⟩-ren wk-ren) V)
                                   (C-rename exch-ren M))
                pV₂ (renᵛ (cong-⟨⟩-ren wk-ren) V pV , renᶜ exch-ren M pM)
            ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (  C-rename-nat exch-ren M pM
                                  ∙ ∘ᵐ-congʳ (exch-ren-mor {Γ} {[ ρ ] A} {B})))
            ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , box-wk B V pV ⟩ᵐ-cong))
            ∙ comm-r (⟦ M ⟧ᶜᵗ pM) _ _)
