---------------------------------------------------------------------------
-- Soundness of `unbox-beta`.                                            --
--                                                                       --
-- Unboxing the variable a `box V` just bound, anywhere inside an        --
-- evaluation context `K`, is substituting `V`. The two sides differ     --
-- only in `K`'s hole and agree only under the ambient `box`, so this is --
-- `fill-cong-env` applied at the box's environment extension            --
-- `g = ⟨ idᵐ , [ ρ ]ᶠ ⟦V⟧ ∘ᵐ η⊣ ⟩`.                                     --
--                                                                       --
-- The hole obligation is the adjunction's triangle: the cell was        --
-- written by `η⊣` and the read is `ε⊣`, and `ε⊣ ∘ ⟨ρ⟩ᶠ η⊣ ≈ idᵐ`.       --
-- Getting there needs `wkc-ext`: the weakening that reaches under `K`'s --
-- binders commutes with extending the environment through them.         --
---------------------------------------------------------------------------

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

module MonomorphicCalculus.EquationalTheory.Soundness.UnboxBeta
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

open import MonomorphicCalculus.Syntax.Types S
open import MonomorphicCalculus.Syntax.Contexts      S
open import MonomorphicCalculus.Syntax.Terms      S
open import MonomorphicCalculus.Syntax.Renaming      S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename)
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  S
       using (∈-++ᶜˡ; grade-++ᶜˡ; grade-++ᶜˡ-𝟏ᵣ; wk-ren-⟨ρ⟩-ctx-img; var-img)
open import MonomorphicCalculus.Syntax.Substitution  S
open import MonomorphicCalculus.Syntax.CompContext   S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ;
                     ⟨⟩-η-nat; ⟨⟩-μ-nat; ⟨⟩-≤-nat; ⟨⟩-idᵐ)
open Adjunction Adj using (η⊣; ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import MonomorphicCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.EquationalTheory.Soundness.Fill S Cat Fut Pst Adj GTy Mon GE

-- Reaching under a context suffix commutes with extending the environment
-- through it. Induction on the suffix, following `wk-ren-⟨ρ⟩-ctx`'s own
-- recursion: `η` at the empty suffix, projection at a value binder, and `μ`
-- at a lock.

wkc-ext : (Γ Γ' Θ : Ctx) → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ' ⟧ᶜᵗˣ)
        → ⟦ wk-ren-⟨ρ⟩-ctx {Γ'} {Θ} refl ⟧ʳ ∘ᵐ ext Γ Γ' Θ g
        ≈ᵐ ⟨ ctx-grade Θ ⟩ᶠ g ∘ᵐ ⟦ wk-ren-⟨ρ⟩-ctx {Γ} {Θ} refl ⟧ʳ
wkc-ext Γ Γ' [] g = ≈ᵐ-sym (⟨⟩-η-nat g)
wkc-ext Γ Γ' (Θ ∷ A) g =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (wkc-ext Γ Γ' Θ g)
  ∙ ∘ᵐ-assoc _ _ _
wkc-ext Γ Γ' (Θ ⟨ ρ ⟩) g =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
  ∙ ∘ᵐ-congʳ (⟨⟩-congᶠ (wkc-ext Γ Γ' Θ g))
  ∙ ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-μ-nat g))
  ∙ ∘ᵐ-assoc _ _ _

sound-unbox-beta : ∀ {Γ A A' C D ρ}
                 → (V : Γ ⟨ ρ ⟩ ⊢ᵛ⦂ A)
                 → (K : Γ ∷ [ ρ ] A ⊢K[ all ◁ D ]⦂ C)
                 → (p : ctx-grade (hole-ctx K) ≾ᵣ ρ)
                 → (u : A <:ᵛ A')
                 → (N : (Γ ∷ [ ρ ] A ++ᶜ hole-ctx K) ∷ A' ⊢ᶜ⦂ D)
                 → Paramᵏ K → Paramᶜ N
                 → Soundᶜ≡ᵗʰ (unbox-beta V K p u N)
sound-unbox-beta {Γ} {A} {A'} {C} {D} {ρ} V K p u N pK pN (pV , pL) (pV' , pR) =
    ⟦⟧ᶜᵗ-irr (box _ V (K [ X ])) (pV , pL) (pV , fillᴾ K pK X pN)
  ∙ fill-cong-env Γ K pK X Y pN pY g hole
  ∙ ≈ᵐ-sym (⟦⟧ᶜᵗ-irr (box _ V (K [ Y ])) (pV' , pR) (pV , fillᴾ K pK Y pY))
  where
    Θ : Ctx
    Θ = hole-ctx K

    -- the renaming that reaches the boxed variable from under `K`
    w : Ren [] ((Γ ∷ [ ρ ] A) ++ᶜ Θ) ((Γ ∷ [ ρ ] A) ⟨ ρ ⟩)
    w = ⟨⟩-≤-ren p ∘ʳ wk-ren-⟨ρ⟩-ctx refl

    -- the same at the un-extended context
    w₀ : Ren [] (Γ ++ᶜ Θ) (Γ ⟨ ρ ⟩)
    w₀ = ⟨⟩-≤-ren p ∘ʳ wk-ren-⟨ρ⟩-ctx refl

    -- the variable that renaming names, and the bound the axiom stores
    xB : [ ρ ] A ∈[ grade-++ᶜˡ 𝟏ᵣ Θ ] ((Γ ∷ [ ρ ] A) ++ᶜ Θ)
    xB = ∈-++ᶜˡ Θ Hd

    relB : grade-++ᶜˡ 𝟏ᵣ Θ ≾ᵣ ρ
    relB = ≾ᵣ-trans (≾ᵣ-reflexive (grade-++ᶜˡ-𝟏ᵣ Θ)) p

    X : (Γ ∷ [ ρ ] A) ++ᶜ Θ ⊢ᶜ⦂ D
    X = unbox xB relB u N

    -- exactly the renaming the axiom's right-hand side uses (`∘ʳ` is a
    -- constructor, so the bracketing matters)
    r₁ : Ren [] ((Γ ∷ [ ρ ] A) ++ᶜ Θ) (Γ ⟨ ρ ⟩)
    r₁ = (cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren p) ∘ʳ wk-ren-⟨ρ⟩-ctx refl

    W : (Γ ∷ [ ρ ] A) ++ᶜ Θ ⊢ᵛ⦂ A'
    W = subV (V-rename r₁ V) u

    Y : (Γ ∷ [ ρ ] A) ++ᶜ Θ ⊢ᶜ⦂ D
    Y = N [ split-[] ↦ W ]c

    pY : Paramᶜ Y
    pY = subᶜ N split-[] W pN (renᵛ r₁ V pV)

    -- the environment `box V` installs
    g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ∷ [ ρ ] A ⟧ᶜᵗˣ
    g = ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ

    G : ⟦ Γ ++ᶜ Θ ⟧ᶜᵗˣ →ᵐ ⟦ (Γ ∷ [ ρ ] A) ++ᶜ Θ ⟧ᶜᵗˣ
    G = ext Γ (Γ ∷ [ ρ ] A) Θ g

    -- Reaching the variable and unboxing it, under the box's environment, is
    -- `V` reindexed: `⟨⟩-≤ p` slides past `⟨ ρ ⟩ᶠ g` (`⟨⟩-≤-nat`), `wkc-ext`
    -- exchanges the weakening with the extension, and then the box's `η⊣` is
    -- cancelled by the read's `ε⊣` (`triangleˡ`).
    w-ext : ⟦ w ⟧ʳ ∘ᵐ G ≈ᵐ ⟨ ρ ⟩ᶠ g ∘ᵐ ⟦ w₀ ⟧ʳ
    w-ext =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (wkc-ext Γ (Γ ∷ [ ρ ] A) Θ g)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (⟨⟩-≤-nat g p))
      ∙ ∘ᵐ-assoc _ _ _

    -- reaching `xB` is reaching the head variable through the lock
    c : 𝟏ᵣ ·ᵣ ρ ≾ᵣ ρ
    c = ≃ᵣ⇒≾ᵣ (·ᵣ-identityˡ ρ)

    wImg : var-img w (Tl-⟨⟩ (Hd {Γ = Γ})) ≡ (grade-++ᶜˡ 𝟏ᵣ Θ , xB)
    wImg = wk-ren-⟨ρ⟩-ctx-img Θ refl (Hd {Γ = Γ})

    relW : proj₁ (var-img w (Tl-⟨⟩ (Hd {Γ = Γ}))) ≾ᵣ ρ
    relW = subst (_≾ᵣ ρ) (sym (cong proj₁ wImg)) relB

    lkw : lk xB relB u ≈ᵐ ⟦ u ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨ ρ ⟩ᶠ sndᵐ ∘ᵐ ⟦ w ⟧ʳ
    lkw =
        lk-irr (sym wImg) relB relW u u
      ∙ ∘ᵐ-congʳ (  unbox-env-nat w (Tl-⟨⟩ (Hd {Γ = Γ})) c relW
                  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (hd-lookup {Δ₀ = Γ} {B = [ ρ ] A} {ρ = ρ} c))
                  ∙ ∘ᵐ-assoc _ _ _)

    lookup : lk xB relB u ∘ᵐ G ≈ᵐ ⟦ u ⟧<:ᵛ ∘ᵐ ⟦ V ⟧ᵛᵗ pV ∘ᵐ ⟦ r₁ ⟧ʳ ∘ᵐ G
    lookup =
        ∘ᵐ-congˡ lkw
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ∘ᵐ-assoc _ _ _
                  ∙ ∘ᵐ-congʳ w-ext
                  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym (⟨⟩-∘ᵐ _ _)
                              ∙ ⟨⟩-congᶠ (⟨⟩ᵐ-sndᵐ _ _)
                              ∙ ⟨⟩-∘ᵐ _ _)
                  ∙ ∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ε⊣-nat _))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                  ∙ ∘ᵐ-congˡ triangleˡ
                  ∙ ∘ᵐ-identityˡ _)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
                          ∙ ∘ᵐ-congʳ w-ext
                          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                          ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym (⟨⟩-∘ᵐ _ _)
                                      ∙ ⟨⟩-congᶠ (⟨⟩ᵐ-fstᵐ _ _)
                                      ∙ ⟨⟩-idᵐ)
                          ∙ ∘ᵐ-identityˡ _)))

    -- the subsumption rides along on both sides
    hole : ⟦ X ⟧ᶜᵗ pN ∘ᵐ G ≈ᵐ ⟦ Y ⟧ᶜᵗ pY ∘ᵐ G
    hole =
        ∘ᵐ-congˡ (unbox-def xB relB u N pN)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                  ∙ ⟨ ∘ᵐ-identityˡ _ , lookup ⟩ᵐ-cong
                  ∙ ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _)
                    , ≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
                              ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (V-rename-nat r₁ V pV)
                                          ∙ ∘ᵐ-assoc _ _ _)) ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat N split-[] W pN (renᵛ r₁ V pV)))
