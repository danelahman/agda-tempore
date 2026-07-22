------------------------------------------------------------------------
-- Soundness of `unbox-beta`.                                           --
--                                                                    --
-- Unboxing the variable a `box V` just bound — anywhere inside an       --
-- evaluation context `K` — is substituting `V`. The two sides differ    --
-- only in `K`'s hole and agree only under the ambient `box`, so this is --
-- `fill-cong-env` applied at the box's environment extension            --
-- `g = ⟨ idᵐ , [ ρ ]ᶠ ⟦V⟧ ∘ᵐ η⊣ ⟩`.                                     --
--                                                                    --
-- The hole obligation is the adjunction's triangle: the cell was        --
-- written by `η⊣` and the read is `ε⊣`, and `ε⊣ ∘ ⟨ρ⟩ᶠ η⊣ ≈ idᵐ`.       --
-- Getting there needs `wkc-ext`: the weakening that reaches under `K`'s --
-- binders commutes with extending the environment through them.        --
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

module EquationalTheory.Soundness.UnboxBeta
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
open import Syntax.CompContext   S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ;
                     ⟨⟩-η-nat; ⟨⟩-μ-nat; ⟨⟩-≤-nat; ⟨⟩-idᵐ)
open Adjunction Adj using (η⊣; ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Fill S Cat Fut Pst Adj GTy Mon GE

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

sound-unbox-beta : ∀ {Γ A C D ρ}
                 → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
                 → (K : Γ ∷ [ ρ ] A ⊢K[ all ◁ D ]⦂ C)
                 → (p : ctx-grade (hole-ctx K) ≾ᵣ ρ)
                 → (N : (Γ ∷ [ ρ ] A ++ᶜ hole-ctx K) ∷ A ⊢C⦂ D)
                 → Paramᵏ K → Paramᶜ N
                 → Soundᶜ== (unbox-beta V K p N)
sound-unbox-beta {Γ} {A} {C} {D} {ρ} V K p N pK pN (pV , pL) (pV' , pR) =
    ⟦⟧ᶜᵗ-irr (box V (K [ X ])) (pV , pL) (pV , fillᴾ K pK X (tt , pN))
  ∙ fill-cong-env Γ K pK X Y (tt , pN) pY g hole
  ∙ ≈ᵐ-sym (⟦⟧ᶜᵗ-irr (box V (K [ Y ])) (pV' , pR) (pV , fillᴾ K pK Y pY))
  where
    Θ : Ctx
    Θ = hole-ctx K

    -- the renaming that reaches the boxed variable from under `K`
    w : Ren ((Γ ∷ [ ρ ] A) ⟨ ρ ⟩) ((Γ ∷ [ ρ ] A) ++ᶜ Θ)
    w = wk-ren-⟨ρ⟩-ctx refl ∘ʳ ⟨⟩-≤-ren p

    -- the same at the un-extended context
    w₀ : Ren (Γ ⟨ ρ ⟩) (Γ ++ᶜ Θ)
    w₀ = wk-ren-⟨ρ⟩-ctx refl ∘ʳ ⟨⟩-≤-ren p

    X : (Γ ∷ [ ρ ] A) ++ᶜ Θ ⊢C⦂ D
    X = unbox w (var (λ _ → ≾ᵣ-refl) Hd) N

    -- exactly the renaming the axiom's right-hand side uses (`∘ʳ` is a
    -- constructor, so the bracketing matters)
    r₁ : Ren (Γ ⟨ ρ ⟩) ((Γ ∷ [ ρ ] A) ++ᶜ Θ)
    r₁ = wk-ren-⟨ρ⟩-ctx refl ∘ʳ (⟨⟩-≤-ren p ∘ʳ cong-⟨⟩-ren wk-ren)

    W : (Γ ∷ [ ρ ] A) ++ᶜ Θ ⊢V⦂ A
    W = V-rename r₁ V

    Y : (Γ ∷ [ ρ ] A) ++ᶜ Θ ⊢C⦂ D
    Y = N [ Hd ↦ W ]c

    pY : Paramᶜ Y
    pY = subᶜ N Hd W pN (renᵛ r₁ V pV)

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

    lookup : lk (proj₁ (proj₂ (unbox⇒var w (var (λ _ → ≾ᵣ-refl) Hd))))
                (proj₂ (proj₂ (unbox⇒var w (var (λ _ → ≾ᵣ-refl) Hd))))
               ∘ᵐ G
           ≈ᵐ ⟦ V ⟧ᵛᵗ pV ∘ᵐ ⟦ r₁ ⟧ʳ ∘ᵐ G
    lookup =
        ∘ᵐ-congˡ (unbox⇒var-Hd w)
      ∙ ∘ᵐ-assoc _ _ _
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
                          ∙ ∘ᵐ-identityˡ _))

    hole : ⟦ X ⟧ᶜᵗ (tt , pN) ∘ᵐ G ≈ᵐ ⟦ Y ⟧ᶜᵗ pY ∘ᵐ G
    hole =
        ∘ᵐ-congˡ (unbox-def w (var (λ _ → ≾ᵣ-refl) Hd) N tt pN)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                  ∙ ⟨ ∘ᵐ-identityˡ _ , lookup ⟩ᵐ-cong
                  ∙ ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _)
                    , ≈ᵐ-sym (  ∘ᵐ-congˡ (V-rename-nat r₁ V pV)
                              ∙ ∘ᵐ-assoc _ _ _) ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (C-subst-nat N Hd W pN (renᵛ r₁ V pV)))
