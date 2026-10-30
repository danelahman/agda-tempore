------------------------------------------------------------------------
-- Soundness of the effect-handling equations.                          --
-- Each is the corresponding `T-alg-of-handlerᵀ-*` law of the model,    --
-- with the handled computation's own former unfolded first.            --
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

module MonomorphicCalculus.EquationalTheory.Soundness.Handle
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

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename)
open import MonomorphicCalculus.Syntax.Substitution    S

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ; []-monoidal; []-monoidal-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; μ; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-μ; ⟨⊤⟩-η-nat; ⟨⊤⟩-μ∘η≡id;
              ⟨⊤⟩-μ∘Tη≡id; free-extᵉ-nat; free-necᵉ-nat; barrier-μ; barrier-lock)

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
open import MonomorphicCalculus.EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE
       using (εᵇ-η⊣-u; str-extend; str-delay)

sound-handle-return : ∀ {Γ A B ε}
  → (V : Γ ⊢V⦂ A)
  → (H : (op : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
  → Soundᶜ== (handle-return V H N)
sound-handle-return {Γ} {A} {B} {ε} V H N (pV , pN , pH , uH) pR =
    handle-in-β (return V) H N pV pN pH uH
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   ∘ᵐ-congʳ (  ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                                ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
                            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                            ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
                            ∙ ∘ᵐ-assoc _ _ _)
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat _))
                ∙ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-ηᵀ (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ} H pH uH))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ εᵇ-η⊣-u {⟦ Γ ⟧ᶜᵗˣ} map-uᵉ
                          , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e ((C-rename r N) [ split-[] ↦ V ]c))
                pR pRc
            ∙ sound-ε-≃ e ((C-rename r N) [ split-[] ↦ V ]c) pRc
            ∙ ∘ᵐ-congʳ (  C-subst-nat (C-rename r N) split-[] V (renᶜ r N pN) pV
                        ∙ ∘ᵐ-congˡ (C-rename-nat r N pN)
                        ∙ ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-identityʳ _
                                        ∙ ∘ᵐ-congˡ (⟨⟩-≤-irr _ _)
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  where
    e = ≃ₑ-sym (·ₑ-identityˡ ε)
    r   = cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-uᵉ) ∘ʳ ⟨⟩-η-ren)
    pRc = subᶜ (C-rename r N) split-[] V (renᶜ r N pN) pV

-- Transports the fold along a clause-family renaming `r` that factors as
-- `⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ g` through the free `⟨⊤⟩`-algebra's universal property.

module Reindex
         {Γ Γ' : Ctx} {B : VType}
         (r : Ren [] (Γ' ⟨ ⊤ᵣ ⟩) (Γ ⟨ ⊤ᵣ ⟩))
         (g : ⟦ Γ' ⟧ᶜᵗˣ →ᵐ ⟨ ⊤ᵣ ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ)
         (r≈ : ⟦ r ⟧ʳ ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ g)
         (H : (op : Op) → (ε'' : E)
            → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         (pH : ∀ op ε'' → Paramᶜ (H op ε''))
         (uH : EffUniformʰ {Γ} H pH)
       where

  Hᵣ : (op : Op) → (ε'' : E)
     → Γ' ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
          ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
  Hᵣ op ε'' = C-rename (cong-∷-ren (cong-∷-ren r)) (H op ε'')

  pHᵣ : ∀ op ε'' → Paramᶜ (Hᵣ op ε'')
  pHᵣ op ε'' = renᶜ (cong-∷-ren (cong-∷-ren r)) (H op ε'') (pH op ε'')

  uHᵣ : EffUniformʰ {Γ'} Hᵣ pHᵣ
  uHᵣ = ren-clauses-uniform r H pH uH

  f : ⟦ Γ' ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
  f = ⟦ r ⟧ʳ

  barrier : f ∘ᵐ ⟨⊤⟩-η ≈ᵐ g
  barrier =
      ∘ᵐ-congˡ r≈
    ∙ ∘ᵐ-assoc _ _ _
    ∙ ∘ᵐ-congʳ (⟨⊤⟩-η-nat g)
    ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ ⟨⊤⟩-μ∘η≡id
    ∙ ∘ᵐ-identityˡ _

  f-necᵉ : ∀ {ρ₀}
         → [ ρ₀ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ (⟨⊤⟩-eternalᵒ ⟦ Γ' ⟧ᶜᵗˣ) {ρ₀}
         ≈ᵐ Eternalᵒ.necᵉ (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) {ρ₀} ∘ᵐ f
  f-necᵉ =
      ∘ᵐ-congˡ ([]-congᶠ r≈)
    ∙ free-necᵉ-nat (⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ g) (free-extᵉ-nat g)
    ∙ ∘ᵐ-congʳ (≈ᵐ-sym r≈)

  -- The renamed family's own certificates are whatever the reduct carries;
  -- `⟦⟧ᶜᵗ-irr` reconciles them with the renamed ones.
  module _ (pH' : ∀ op ε'' → Paramᶜ (Hᵣ op ε''))
           (uH' : EffUniformʰ {Γ'} Hᵣ pH')
         where

    clause-nat : ∀ op ε''
               → clauseᵀ (⟦_⟧ʰᵗ {Γ'} Hᵣ pH' uH') op ε''
               ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
    clause-nat op ε'' =
        ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (Hᵣ op ε'') (pH' op ε'') (pHᵣ op ε'')
                  ∙ C-rename-nat (cong-∷-ren (cong-∷-ren r))
                      (H op ε'') (pH op ε''))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (adapt-commute _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    alg-nat : ∀ {ε ε'}
            → T-alg-of-handlerᵀ {_} {_} {ε} {ε'}
                (⟨⊤⟩-eternalᵒ ⟦ Γ' ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ'} Hᵣ pH' uH')
            ≈ᵐ T-alg-of-handlerᵀ {_} {_} {ε} {ε'}
                 (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ} H pH uH)
               ∘ᵐ mapˣᵐ f idᵐ
    alg-nat =
      T-alg-of-handlerᵀ-natᴾ (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟨⊤⟩-eternalᵒ ⟦ Γ' ⟧ᶜᵗˣ)
        f f-necᵉ (⟦_⟧ʰᵗ {Γ} H pH uH) (⟦_⟧ʰᵗ {Γ'} Hᵣ pH' uH') clause-nat

-- `handle-box`, `handle-unbox`: a binder commutes with handling by any
-- handler value, which is weakened past it.

handle-wk : ∀ {Γ A B C ε ε'}
          → (W : Γ ⊢V⦂ (B ‼ ε) ⇛ (C ‼ ε')) → (pW : Paramᵛ W)
          → (pW' : Paramᵛ (V-rename (wk-ren {Δ = Γ} {A = A}) W))
          → (m : ⟦ Γ ∷ A ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ B ⟧ᵛ ε)
          → (g : ⟦ Γ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ∷ A ⟧ᶜᵗˣ) → fstᵐ ∘ᵐ g ≈ᵐ idᵐ
          → appʰ ≾ₑ-refl ∘ᵐ ⟨ ⟦ W ⟧ᵛᵗ pW , m ∘ᵐ g ⟩ᵐ
          ≈ᵐ (appʰ ≾ₑ-refl ∘ᵐ ⟨ ⟦ V-rename wk-ren W ⟧ᵛᵗ pW' , m ⟩ᵐ) ∘ᵐ g
handle-wk W pW pW' m g fg =
  ≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                      ∙ ⟨   ∘ᵐ-congˡ (  ⟦⟧ᵛᵗ-irr (V-rename wk-ren W) pW' (renᵛ wk-ren W pW)
                                      ∙ V-rename-nat wk-ren W pW)
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ fg
                          ∙ ∘ᵐ-identityʳ _
                        , ≈ᵐ-refl ⟩ᵐ-cong))

sound-handle-box : ∀ {Γ A B C ρ ε ε'}
  → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
  → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
  → (W : Γ ⊢V⦂ (B ‼ ε) ⇛ (C ‼ ε'))
  → Soundᶜ== (handle-box V M W)
sound-handle-box {ρ = ρ} V M W ((pV , pM) , pW) (pV₂ , pM₂ , pW₂) =
    handle-wk W pW pW₂ (⟦ M ⟧ᶜᵗ pM) gb (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ∘ᵐ-cong (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ⟦⟧ᶜᵗ-irr M pM pM₂ ⟩ᵐ-cong)
            ⟨ ≈ᵐ-refl , ∘ᵐ-congˡ ([]-congᶠ (⟦⟧ᵛᵗ-irr V pV pV₂)) ⟩ᵐ-cong
  where
    gb = ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ

sound-handle-unbox : ∀ {Γ A A₀ B C ρ₀ ρ' ε ε'}
  → (x : [ ρ₀ ] A₀ ∈[ ρ' ] Γ)
  → (rel : ρ' ≾ᵣ ρ₀)
  → (w : A₀ <:ᵛ A)
  → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
  → (V : Γ ⊢V⦂ (B ‼ ε) ⇛ (C ‼ ε'))
  → Soundᶜ== (handle-unbox x rel w M V)
sound-handle-unbox x rel w M V (pM , pV) (pM₂ , pV₂) =
    handle-wk V pV pV₂ (⟦ M ⟧ᶜᵗ pM) gu (⟨⟩ᵐ-fstᵐ _ _)
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ⟦⟧ᶜᵗ-irr M pM pM₂ ⟩ᵐ-cong)
  where
    gu = ⟨ idᵐ , ⟦ w ⟧<:ᵛ ∘ᵐ ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ

-- `handle-delay`: the handled computation's `delay` becomes a `delay` of the
-- handled computation.

sound-handle-delay : ∀ {Γ A B τ ε ε'}
  → (M : Γ ⟨ of-durʳ τ ⟩ ⊢C⦂ A ‼ ε)
  → (H : (op : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ (of-durᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
  → Soundᶜ== (handle-delay M H N)
sound-handle-delay {Γ} {A} {B} {τ} {ε} {ε'} M H N (pM , pN , pH , uH) pR =
    handle-in-β (delay τ M) H N pM pN pH uH
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , str-delay τ (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-delayᵀ τ (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ} H pH uH))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨   ∘ᵐ-congˡ (Eternalᵒ.necᵉ-mate (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ))
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟨⊤⟩-η))
                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
                      ∙ ∘ᵐ-congˡ ([]-congᶠ (barrier-lock ∙ ≈ᵐ-sym R.barrier))
                    , ∘ᵐ-identityˡ _ ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-monoidal-nat _ _))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ η⊣-monoidal
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                  ∙ []-congᶠ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                              ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (  ≈ᵐ-sym ([]-∘ᵐ _ _)
                  ∙ []-congᶠ (
                        ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                                  , ∘ᵐ-congˡ (≈ᵐ-sym (
                                        T-congᶠ (C-rename-nat r N pN)
                                      ∙ T-congᶠ (∘ᵐ-congʳ (mapˣᵐ-cong
                                          (∘ᵐ-congˡ (⟨⟩-≤-irr _ _))
                                          ≈ᵐ-refl)))) ⟩ᵐ-cong)
                      ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-refl , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong
                                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (R.alg-nat R.pHᵣ R.uHᵣ))))))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-≃ e (delay τ (handle M `with R.Hᵣ `in (C-rename r N))))
                pR pRc
            ∙ sound-ε-≃ e (delay τ (handle M `with R.Hᵣ `in (C-rename r N))) pRc
            ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ
                (handle-in-β M R.Hᵣ (C-rename r N) pM (renᶜ r N pN) R.pHᵣ R.uHᵣ)))))
  where
    e = ≃ₑ-sym (·ₑ-assoc (of-durᵉ τ) ε ε')
    r   = cong-∷-ren (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ (≃ᵣ-trans map-·ᵉ (·ᵣ-cong map-of-durᵉ ≃ᵣ-refl)))
                      ∘ʳ ⟨⟩-μ-ren)

    module R = Reindex (⟨⟩-≤-ren (≾-⊤ᵣ _) ∘ʳ ⟨⟩-μ-ren)
                       (⟨⟩-≤ (≾-⊤ᵣ (of-durʳ τ))) (barrier-μ (≾-⊤ᵣ _)) H pH uH

    pRc = pM , renᶜ r N pN , R.pHᵣ , R.uHᵣ
