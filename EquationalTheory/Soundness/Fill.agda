------------------------------------------------------------------------
-- Filling a computation term context is a congruence.                  --
--                                                                    --
-- `unbox-beta` (unlike the other axioms) equates two terms that differ  --
-- only *inside* an evaluation context `K`, so its soundness needs       --
-- `fill-cong`: denotationally equal fillings give denotationally equal  --
-- filled terms. Proved by induction on `K`; every case is the           --
-- corresponding term former's congruence, with the `C-rename (eq-ren …)` --
-- that `_[_]` inserts at each binder discharged by `C-rename-nat` on     --
-- both sides.                                                          --
--                                                                    --
-- `Paramᵏ` collects the certificates of a context's *non-hole* parts,   --
-- and `fillᴾ` assembles the filled term's certificate from it.          --
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
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣)
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

-- The certificates a computation term context carries, i.e. those of every
-- sub-term other than the hole.

Paramᵏ : ∀ {Γ f CH C} → Γ ⊢K[ f ◁ CH ]⦂ C → Set
Paramᵏ []ₖ                        = ⊤
Paramᵏ (K ₖ[ p ]⨟ N)              = Paramᵏ K × Paramᶜ N
Paramᵏ (perform[ p ]ₖ op V K)     = Paramᵛ V × Paramᵏ K
Paramᵏ (delay[ p ]ₖ τ K)          = Paramᵏ K
Paramᵏ (unbox[ p ]ₖ w V K)        = Paramᵛ V × Paramᵏ K
Paramᵏ (box[ p ]ₖ V K)            = Paramᵛ V × Paramᵏ K
Paramᵏ {Γ} (handle[_]ₖ_`with_`in {B = B} p K H N) =
  Paramᵏ K × Paramᶜ N ×
  Σ[ pH ∈ (∀ op ε'' Γ' → Paramᶜ (H op ε'' Γ')) ]
    (EffUniformʰ {Γ} {B} H pH × CtxUniformʰ {Γ} {B} H pH)

-- The filled term's certificate.

fillᴾ : ∀ {Γ f CH C} → (K : Γ ⊢K[ f ◁ CH ]⦂ C) → Paramᵏ K
      → (N : Γ ++ᶜ hole-ctx K ⊢C⦂ CH) → Paramᶜ N
      → Paramᶜ (K [ N ])
fillᴾ []ₖ                    _          N pN = pN
fillᴾ (K ₖ[ p ]⨟ M)          (pK , pM)  N pN = fillᴾ K pK N pN , pM
fillᴾ (perform[ p ]ₖ op V K) (pV , pK)  N pN = pV , fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (delay[ p ]ₖ τ K)      pK         N pN = fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (unbox[ p ]ₖ w V K)    (pV , pK)  N pN = pV , fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (box[ p ]ₖ V K)        (pV , pK)  N pN = pV , fillᴾ K pK _ (renᶜ _ N pN)
fillᴾ (handle[ p ]ₖ K `with H `in M) (pK , pM , pH , uH , cH) N pN =
  fillᴾ K pK N pN , pM , pH , uH , cH

-- Filling is a congruence: replacing the hole's filling by a denotationally
-- equal one leaves the filled term's denotation unchanged.

fill-cong : ∀ {Γ f CH C} → (K : Γ ⊢K[ f ◁ CH ]⦂ C) → (pK : Paramᵏ K)
          → {N N' : Γ ++ᶜ hole-ctx K ⊢C⦂ CH}
          → (pN : Paramᶜ N) → (pN' : Paramᶜ N')
          → ⟦ N ⟧ᶜᵗ pN ≈ᵐ ⟦ N' ⟧ᶜᵗ pN'
          → ⟦ K [ N ] ⟧ᶜᵗ (fillᴾ K pK N pN) ≈ᵐ ⟦ K [ N' ] ⟧ᶜᵗ (fillᴾ K pK N' pN')

-- The filling reindexed by the binder's context coercion — the shape the
-- recursive cases hand to the induction hypothesis. The renaming has to be
-- named at each use (it is the `eq-ren` that `_[_]` inserts): it occurs under
-- `⟦_⟧ᶜᵗ`, which is not injective, so Agda cannot recover it from the goal.
ren-cong : ∀ {Γ Γ' CH} → (r : Ren Γ Γ')
         → (N N' : Γ ⊢C⦂ CH) → (pN : Paramᶜ N) → (pN' : Paramᶜ N')
         → ⟦ N ⟧ᶜᵗ pN ≈ᵐ ⟦ N' ⟧ᶜᵗ pN'
         → ⟦ C-rename r N ⟧ᶜᵗ (renᶜ r N pN)
         ≈ᵐ ⟦ C-rename r N' ⟧ᶜᵗ (renᶜ r N' pN')
ren-cong r N N' pN pN' eq =
    C-rename-nat r N pN
  ∙ ∘ᵐ-congˡ eq
  ∙ ≈ᵐ-sym (C-rename-nat r N' pN')

fill-cong []ₖ _ pN pN' eq = eq
fill-cong (K ₖ[ p ]⨟ M) (pK , pM) pN pN' eq =
  ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , fill-cong K pK pN pN' eq ⟩ᵐ-cong))
fill-cong (handle[ p ]ₖ K `with H `in M) (pK , pM , pH , uH , cH) pN pN' eq =
  ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
            , ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , fill-cong K pK pN pN' eq ⟩ᵐ-cong)
            ⟩ᵐ-cong)
fill-cong {Γ} (perform[_]ₖ {A} {ε} p op V K) (pV , pK) {N} {N'} pN pN' eq =
  ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
            , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (substᵈ-≈ (ty-gty (arity op))
                (fill-cong K pK (renᶜ r N pN) (renᶜ r N' pN')
                   (ren-cong r N N' pN pN' eq))))) ⟩ᵐ-cong)
  where
    r : Ren (Γ ++ᶜ hole-ctx (perform[ p ]ₖ op V K))
            ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ++ᶜ hole-ctx K)
    r = eq-ren (trans
          (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
          (sym (++ᶜ-assoc Γ ([] ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
                            (hole-ctx K))))
fill-cong {Γ} (delay[_]ₖ {A} {ε} p τ K) pK {N} {N'} pN pN' eq =
  ∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ
    (fill-cong K pK (renᶜ r N pN) (renᶜ r N' pN') (ren-cong r N N' pN pN' eq))))
  where
    r : Ren (Γ ++ᶜ hole-ctx (delay[ p ]ₖ τ K))
            ((Γ ⟨ of-natʳ τ ⟩) ++ᶜ hole-ctx K)
    r = eq-ren (trans
          (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
          (sym (++ᶜ-assoc Γ ([] ⟨ of-natʳ τ ⟩) (hole-ctx K))))
fill-cong {Γ} (unbox[_]ₖ {A} {C} {ρ} {Δ} p w V K) (pV , pK) {N} {N'} pN pN' eq =
    unbox-def w V (K [ C-rename r N ]) pV (fillᴾ K pK (C-rename r N) (renᶜ r N pN))
  ∙ ∘ᵐ-congˡ (fill-cong K pK (renᶜ r N pN) (renᶜ r N' pN')
                (ren-cong r N N' pN pN' eq))
  ∙ ≈ᵐ-sym (unbox-def w V (K [ C-rename r N' ]) pV
              (fillᴾ K pK (C-rename r N') (renᶜ r N' pN')))
  where
    r : Ren (Γ ++ᶜ hole-ctx (unbox[ p ]ₖ w V K)) ((Γ ∷ A) ++ᶜ hole-ctx K)
    r = eq-ren (trans
          (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
          (sym (++ᶜ-assoc Γ ([] ∷ A) (hole-ctx K))))
fill-cong {Γ} (box[_]ₖ {A} {C} {ρ} p V K) (pV , pK) {N} {N'} pN pN' eq =
  ∘ᵐ-congˡ (fill-cong K pK (renᶜ r N pN) (renᶜ r N' pN')
              (ren-cong r N N' pN pN' eq))
  where
    r : Ren (Γ ++ᶜ hole-ctx (box[ p ]ₖ V K)) ((Γ ∷ [ ρ ] A) ++ᶜ hole-ctx K)
    r = eq-ren (trans
          (cong (Γ ++ᶜ_) (rel-hole-ctx-++ᶜ K))
          (sym (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) (hole-ctx K))))
