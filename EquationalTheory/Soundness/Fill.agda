------------------------------------------------------------------------
-- Filling a computation term context is a congruence.                  --
-- Equal fillings denote equal filled terms.                            --
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

module EquationalTheory.Soundness.Fill
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

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Types         S
open import Syntax.Contexts      S
open import Syntax.Language      S
open import Syntax.Renamings     S
open import Syntax.RenActions    S using (C-rename)
open import Syntax.CompContext   S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-∘ᵐ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; ⟨⟩-idᵐ; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ)
open Adjunction Adj using (η⊣; η⊣-nat)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE

-- The certificates a computation term context carries, i.e. those of every
-- sub-term other than the hole.

Paramᵏ : ∀ {Γ f CH C} → Γ ⊢K[ f ◁ CH ]⦂ C → Set
Paramᵏ []ₖ                        = ⊤
Paramᵏ (coerce[ p ]ₖ q K)         = Paramᵏ K
Paramᵏ (K ₖ[ p ]⨟ N)              = Paramᵏ K × Paramᶜ N
Paramᵏ (perform[ p ]ₖ op V K)     = Paramᵛ V × Paramᵏ K
Paramᵏ (delay[ p ]ₖ τ K)          = Paramᵏ K
Paramᵏ (unbox[ p ]ₖ x rel K)      = Paramᵏ K
Paramᵏ (box[ p ]ₖ V K)            = Paramᵛ V × Paramᵏ K
Paramᵏ {Γ} (handle[_]ₖ_`with_`in {B = B} p K H N) =
  Paramᵏ K × Paramᶜ N ×
  Σ[ pH ∈ (∀ op ε'' → Paramᶜ (H op ε'')) ] EffUniformʰ {Γ} {B} H pH

-- The filled term's certificate.

fillᴾ : ∀ {Γ f CH C} → (K : Γ ⊢K[ f ◁ CH ]⦂ C) → Paramᵏ K
      → (N : Γ ++ᶜ hole-ctx K ⊢C⦂ CH) → Paramᶜ N
      → Paramᶜ (K [ N ])
fillᴾ []ₖ                    _          N pN = pN
fillᴾ (coerce[ p ]ₖ q K)     pK         N pN = fillᴾ K pK N pN
fillᴾ (K ₖ[ p ]⨟ M)          (pK , pM)  N pN = fillᴾ K pK N pN , pM
fillᴾ (perform[ p ]ₖ op V K) (pV , pK)  N pN = pV , fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (delay[ p ]ₖ τ K)      pK         N pN = fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (unbox[ p ]ₖ x rel K)  pK         N pN = fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (box[ p ]ₖ V K)        (pV , pK)  N pN = pV , fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (handle[ p ]ₖ K `with H `in M) (pK , pM , pH , uH) N pN =
  fillᴾ K pK N pN , pM , pH , uH

-- The two coercions `_[_]` inserts at a binder, combined.

fill-ext : (Γ Γ' Θ₁ : Ctx) → ∀ {Δ f CH C} → (K : Δ ⊢K[ f ◁ CH ]⦂ C)
         → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ)
         → ⟦ eq-ren (trans (cong (Γ' ++ᶜ_) (rel-hole-ctx-++ᶜ {Δ} {Θ₁} {[]} K))
                           (sym (++ᶜ-assoc Γ' Θ₁ (hole-ctx K)))) ⟧ʳ
             ∘ᵐ ext (Γ ++ᶜ Θ₁) (Γ' ++ᶜ Θ₁) (hole-ctx K) (ext Γ Γ' Θ₁ g)
         ≈ᵐ ext Γ Γ' (rel-hole-ctx K Θ₁) g
             ∘ᵐ ⟦ eq-ren (trans (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ {Δ} {Θ₁} {[]} K))
                                (sym (++ᶜ-assoc Γ Θ₁ (hole-ctx K)))) ⟧ʳ
fill-ext Γ Γ' Θ₁ K g =
    ∘ᵐ-congˡ (eq-ren-trans (cong (Γ' ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                           (sym (++ᶜ-assoc Γ' Θ₁ (hole-ctx K))))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (ext-++ᶜ Γ Γ' g Θ₁ (hole-ctx K))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (ext-eq Γ Γ' g (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym
      (eq-ren-trans (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                    (sym (++ᶜ-assoc Γ Θ₁ (hole-ctx K)))))

-- Transporting the hypothesis across a binder's coercion.

ren-hyp : (Γ Γ' Θ₁ : Ctx) → ∀ {Δ f CH C} → (K : Δ ⊢K[ f ◁ CH ]⦂ C)
        → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ)
        → (rΓ' : Ren [] ((Γ' ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ' ++ᶜ rel-hole-ctx K Θ₁))
        → (rΓ : Ren [] ((Γ ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ ++ᶜ rel-hole-ctx K Θ₁))
        → ⟦ rΓ' ⟧ʳ ∘ᵐ ext (Γ ++ᶜ Θ₁) (Γ' ++ᶜ Θ₁) (hole-ctx K) (ext Γ Γ' Θ₁ g)
          ≈ᵐ ext Γ Γ' (rel-hole-ctx K Θ₁) g ∘ᵐ ⟦ rΓ ⟧ʳ
        → (N N' : Γ' ++ᶜ rel-hole-ctx K Θ₁ ⊢C⦂ CH)
        → (pN : Paramᶜ N) → (pN' : Paramᶜ N')
        → ⟦ N ⟧ᶜᵗ pN ∘ᵐ ext Γ Γ' (rel-hole-ctx K Θ₁) g
          ≈ᵐ ⟦ N' ⟧ᶜᵗ pN' ∘ᵐ ext Γ Γ' (rel-hole-ctx K Θ₁) g
        → ⟦ C-rename rΓ' N ⟧ᶜᵗ (renᶜ rΓ' N pN)
            ∘ᵐ ext (Γ ++ᶜ Θ₁) (Γ' ++ᶜ Θ₁) (hole-ctx K) (ext Γ Γ' Θ₁ g)
          ≈ᵐ ⟦ C-rename rΓ' N' ⟧ᶜᵗ (renᶜ rΓ' N' pN')
            ∘ᵐ ext (Γ ++ᶜ Θ₁) (Γ' ++ᶜ Θ₁) (hole-ctx K) (ext Γ Γ' Θ₁ g)
ren-hyp Γ Γ' Θ₁ K g rΓ' rΓ coh N N' pN pN' eq =
    ∘ᵐ-congˡ (C-rename-nat rΓ' N pN)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ coh
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ eq
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym coh)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-rename-nat rΓ' N' pN'))

-- The hypothesis may assume the ambient morphism `g` extended through `K`;
-- `unbox-beta` needs this since its two fillings agree only under `box V`.

fill-cong-env : (Γ : Ctx) → ∀ {Γ' f CH C} → (K : Γ' ⊢K[ f ◁ CH ]⦂ C)
              → (pK : Paramᵏ K)
              → (N N' : Γ' ++ᶜ hole-ctx K ⊢C⦂ CH)
              → (pN : Paramᶜ N) → (pN' : Paramᶜ N')
              → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ)
              → ⟦ N ⟧ᶜᵗ pN ∘ᵐ ext Γ Γ' (hole-ctx K) g
              ≈ᵐ ⟦ N' ⟧ᶜᵗ pN' ∘ᵐ ext Γ Γ' (hole-ctx K) g
              → ⟦ K [ N ] ⟧ᶜᵗ (fillᴾ K pK N pN) ∘ᵐ g
              ≈ᵐ ⟦ K [ N' ] ⟧ᶜᵗ (fillᴾ K pK N' pN') ∘ᵐ g

fill-cong-env Γ []ₖ _ N N' pN pN' g eq = eq

-- a coercion denotes `T-≤ q`, which the two sides share
fill-cong-env Γ (coerce[ p ]ₖ q K) pK N N' pN pN' g eq =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (fill-cong-env Γ K pK N N' pN pN' g eq)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

fill-cong-env Γ (K ₖ[ p ]⨟ M) (pK , pM) N N' pN pN' g eq =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                                      ∙ ⟨ ≈ᵐ-refl
                                        , fill-cong-env Γ K pK N N' pN pN' g eq
                                        ⟩ᵐ-cong
                                      ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

fill-cong-env Γ (handle[ p ]ₖ K `with H `in M) (pK , pM , pH , uH)
              N N' pN pN' g eq =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ≈ᵐ-refl
                ,   ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                              ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                                          ∙ ⟨ ≈ᵐ-refl
                                            , fill-cong-env Γ K pK N N' pN pN' g eq
                                            ⟩ᵐ-cong
                                          ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
                              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _) ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

fill-cong-env Γ {Γ'} (delay[_]ₖ {A} {ε} p τ K) pK N N' pN pN' g eq =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat g))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _) ∙ []-congᶠ ih ∙ []-∘ᵐ _ _)
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (η⊣-nat g)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    Θ₁ : Ctx
    Θ₁ = [] ⟨ of-natʳ τ ⟩

    rΓ' : Ren [] ((Γ' ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ' ++ᶜ rel-hole-ctx K Θ₁)
    rΓ' = eq-ren (trans (cong (Γ' ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                        (sym (++ᶜ-assoc Γ' Θ₁ (hole-ctx K))))

    rΓ : Ren [] ((Γ ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ ++ᶜ rel-hole-ctx K Θ₁)
    rΓ = eq-ren (trans (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                       (sym (++ᶜ-assoc Γ Θ₁ (hole-ctx K))))

    ih : ⟦ K [ C-rename rΓ' N ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N) (renᶜ rΓ' N pN))
           ∘ᵐ ext Γ Γ' Θ₁ g
       ≈ᵐ ⟦ K [ C-rename rΓ' N' ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N') (renᶜ rΓ' N' pN'))
           ∘ᵐ ext Γ Γ' Θ₁ g
    ih = fill-cong-env (Γ ++ᶜ Θ₁) K pK
           (C-rename rΓ' N) (C-rename rΓ' N')
           (renᶜ rΓ' N pN) (renᶜ rΓ' N' pN')
           (ext Γ Γ' Θ₁ g)
           (ren-hyp Γ Γ' Θ₁ K g rΓ' rΓ (fill-ext Γ Γ' Θ₁ K g) N N' pN pN' eq)

fill-cong-env Γ {Γ'} (unbox[_]ₖ {A} {C} {ρ} p x rel K) pK
              N N' pN pN' g eq =
    ∘ᵐ-congˡ (unbox-def x rel (K [ C-rename rΓ' N ])
                (fillᴾ K pK (C-rename rΓ' N) (renᶜ rΓ' N pN)))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ih
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
              ∙ ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (unbox-def x rel (K [ C-rename rΓ' N' ])
                       (fillᴾ K pK (C-rename rΓ' N') (renᶜ rΓ' N' pN'))))
  where
    Θ₁ : Ctx
    Θ₁ = [] ∷ A

    rΓ' : Ren [] ((Γ' ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ' ++ᶜ rel-hole-ctx K Θ₁)
    rΓ' = eq-ren (trans (cong (Γ' ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                        (sym (++ᶜ-assoc Γ' Θ₁ (hole-ctx K))))

    rΓ : Ren [] ((Γ ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ ++ᶜ rel-hole-ctx K Θ₁)
    rΓ = eq-ren (trans (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                       (sym (++ᶜ-assoc Γ Θ₁ (hole-ctx K))))

    ih : ⟦ K [ C-rename rΓ' N ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N) (renᶜ rΓ' N pN))
           ∘ᵐ ext Γ Γ' Θ₁ g
       ≈ᵐ ⟦ K [ C-rename rΓ' N' ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N') (renᶜ rΓ' N' pN'))
           ∘ᵐ ext Γ Γ' Θ₁ g
    ih = fill-cong-env (Γ ++ᶜ Θ₁) K pK
           (C-rename rΓ' N) (C-rename rΓ' N')
           (renᶜ rΓ' N pN) (renᶜ rΓ' N' pN')
           (ext Γ Γ' Θ₁ g)
           (ren-hyp Γ Γ' Θ₁ K g rΓ' rΓ (fill-ext Γ Γ' Θ₁ K g) N N' pN pN' eq)

fill-cong-env Γ {Γ'} (box[_]ₖ {A} {C} {ρ} p V K) (pV , pK) N N' pN pN' g eq =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ ih
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
              ∙ ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    Θ₁ : Ctx
    Θ₁ = [] ∷ [ ρ ] A

    rΓ' : Ren [] ((Γ' ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ' ++ᶜ rel-hole-ctx K Θ₁)
    rΓ' = eq-ren (trans (cong (Γ' ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                        (sym (++ᶜ-assoc Γ' Θ₁ (hole-ctx K))))

    rΓ : Ren [] ((Γ ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ ++ᶜ rel-hole-ctx K Θ₁)
    rΓ = eq-ren (trans (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                       (sym (++ᶜ-assoc Γ Θ₁ (hole-ctx K))))

    ih : ⟦ K [ C-rename rΓ' N ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N) (renᶜ rΓ' N pN))
           ∘ᵐ ext Γ Γ' Θ₁ g
       ≈ᵐ ⟦ K [ C-rename rΓ' N' ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N') (renᶜ rΓ' N' pN'))
           ∘ᵐ ext Γ Γ' Θ₁ g
    ih = fill-cong-env (Γ ++ᶜ Θ₁) K pK
           (C-rename rΓ' N) (C-rename rΓ' N')
           (renᶜ rΓ' N pN) (renᶜ rΓ' N' pN')
           (ext Γ Γ' Θ₁ g)
           (ren-hyp Γ Γ' Θ₁ K g rΓ' rΓ (fill-ext Γ Γ' Θ₁ K g) N N' pN pN' eq)

fill-cong-env Γ {Γ'} (perform[_]ₖ {A} {ε} p op V K) (pV , pK) N N' pN pN' g eq =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ≈ᵐ-refl , qstep ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  where
    Θ₁ : Ctx
    Θ₁ = [] ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)

    rΓ' : Ren [] ((Γ' ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ' ++ᶜ rel-hole-ctx K Θ₁)
    rΓ' = eq-ren (trans (cong (Γ' ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                        (sym (++ᶜ-assoc Γ' Θ₁ (hole-ctx K))))

    rΓ : Ren [] ((Γ ++ᶜ Θ₁) ++ᶜ hole-ctx K) (Γ ++ᶜ rel-hole-ctx K Θ₁)
    rΓ = eq-ren (trans (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ {_} {Θ₁} {[]} K))
                       (sym (++ᶜ-assoc Γ Θ₁ (hole-ctx K))))

    ih : ⟦ K [ C-rename rΓ' N ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N) (renᶜ rΓ' N pN))
           ∘ᵐ ext Γ Γ' Θ₁ g
       ≈ᵐ ⟦ K [ C-rename rΓ' N' ] ⟧ᶜᵗ
             (fillᴾ K pK (C-rename rΓ' N') (renᶜ rΓ' N' pN'))
           ∘ᵐ ext Γ Γ' Θ₁ g
    ih = fill-cong-env (Γ ++ᶜ Θ₁) K pK
           (C-rename rΓ' N) (C-rename rΓ' N')
           (renᶜ rΓ' N pN) (renᶜ rΓ' N' pN')
           (ext Γ Γ' Θ₁ g)
           (ren-hyp Γ Γ' Θ₁ K g rΓ' rΓ (fill-ext Γ Γ' Θ₁ K g) N N' pN pN' eq)

    qstep = ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat g))
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                      ∙ []-congᶠ (  ≈ᵐ-sym (curryᵐ-nat _ _)
                                  ∙ curryᵐ-cong (≡→≈ᵐ (substᵈ-∘ (ty-gty (arity op)) _ _))
                                  ∙ curryᵐ-cong (substᵈ-≈ (ty-gty (arity op)) ih)
                                  ∙ curryᵐ-cong (≡→≈ᵐ (sym (substᵈ-∘ (ty-gty (arity op)) _ _)))
                                  ∙ curryᵐ-nat _ _)
                      ∙ []-∘ᵐ _ _)
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (η⊣-nat g)
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
