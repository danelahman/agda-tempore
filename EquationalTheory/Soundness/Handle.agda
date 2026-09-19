------------------------------------------------------------------------
-- Soundness of the effect-handling equations.                          --
-- Each is the corresponding `T-alg-of-handlerᵀ-*` law of the model,    --
-- with the handled computation's own former unfolded first.            --
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

module EquationalTheory.Soundness.Handle
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
open import Syntax.RenActions    S using (V-rename; C-rename)
open import Syntax.Substitutions S

open import EquationalTheory.EquationalTheory S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-∘ᵐ; []-congᶠ; []-monoidal; []-monoidal-nat)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; μ)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open Monad Mon

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-μ; ⟨⊤⟩-η-nat; ⟨⊤⟩-μ∘η≡id;
              ⟨⊤⟩-μ∘Tη≡id; free-extᵉ-nat; free-necᵉ-nat; barrier-μ; barrier-lock)

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE
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
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
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
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst e ((C-rename r N) [ split-[] ↦ V ]c))
                pR (ε-substᴾ e _ pRc)
            ∙ sound-ε-subst e ((C-rename r N) [ split-[] ↦ V ]c) pRc
            ∙ ∘ᵐ-congʳ (  C-subst-nat (C-rename r N) split-[] V (renᶜ r N pN) pV
                        ∙ ∘ᵐ-congˡ (C-rename-nat r N pN)
                        ∙ ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-identityʳ _
                                        ∙ ∘ᵐ-congˡ (eq-ren-grade {Γ} map-uᵉ)
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  where
    e   = sym (·ₑ-identityˡ ε)
    r   = cong-∷-ren (eq-ren (cong (Γ ⟨_⟩) map-uᵉ) ∘ʳ ⟨⟩-η-ren)
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

-- Crossing a binder: weakening under the barrier is the free-algebra morphism
-- induced by the barrier itself.

wk-free : ∀ {Γ A}
        → ⟦ cong-⟨⟩-ren {[]} {Γ ∷ A} {Γ} {⊤ᵣ} wk-ren ⟧ʳ
        ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ (⟨⊤⟩-η ∘ᵐ fstᵐ)
wk-free =
  ≈ᵐ-sym (  ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
          ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-congˡ ⟨⊤⟩-μ∘Tη≡id
          ∙ ∘ᵐ-identityˡ _)

-- `handle-box`: a `box` binder commutes with handling.

sound-handle-box : ∀ {Γ A B C ρ ε ε'}
  → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
  → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
  → (H : (op : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
         ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
  → Soundᶜ== (handle-box V M H N)
sound-handle-box {Γ} {A} {B} {C} {ρ} V M H N ((pV , pM) , pN , pH , uH)
                 (pV₂ , pM₂ , pN₂ , pH₂ , uH₂) =
  ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (box V (handle M `with R.Hᵣ `in (C-rename r N)))
              (pV₂ , (pM₂ , pN₂ , pH₂ , uH₂))
              (pV , (pM , renᶜ r N pN , pH₂ , uH₂))
          ∙ ∘ᵐ-congˡ (  ∘ᵐ-congˡ (R.alg-nat pH₂ uH₂)
                      ∙ ∘ᵐ-assoc _ _ _
                      ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                  ∙ ⟨ R.barrier , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                      ∙ ⟨   ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                          ∙ ∘ᵐ-identityʳ _
                        ,   ∘ᵐ-congˡ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN)))
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                          ∙ str-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) gb fstᵐ
                              (⟨⟩ᵐ-fstᵐ _ _) ⟩ᵐ-cong))
  where
    r  = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    gb = ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ

    module R = Reindex (cong-⟨⟩-ren (wk-ren {Δ = Γ} {A = [ ρ ] A}))
                       (⟨⊤⟩-η ∘ᵐ fstᵐ) (wk-free {Γ} {[ ρ ] A}) H pH uH

-- `handle-unbox`: the same for an `unbox` binder.

sound-handle-unbox : ∀ {Γ A B C ρ ρ' ε ε'}
  → (x : [ ρ ] A ∈[ ρ' ] Γ)
  → (rel : ρ' ≾ᵣ ρ)
  → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
  → (H : (op : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
         ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
  → Soundᶜ== (handle-unbox x rel M H N)
sound-handle-unbox {Γ} {A} {B} {C} {ρ} {ρ'} {ε} {ε'} x rel M H N
                   (pM , pN , pH , uH)
                   (pM₂ , pN₂ , pH₂ , uH₂) =
  ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox x rel (handle M `with R.Hᵣ `in (C-rename r N)))
              (pM₂ , pN₂ , pH₂ , uH₂)
              (pM , renᶜ r N pN , pH₂ , uH₂)
          ∙ unbox-def x rel (handle M `with R.Hᵣ `in (C-rename r N))
              (pM , renᶜ r N pN , pH₂ , uH₂)
          ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ (R.alg-nat pH₂ uH₂))
          ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (mapˣᵐ-∘⟨⟩ _ _ _ _)
                      ∙ ⟨⟩ᵐ-∘ _ _ _
                      ∙ ⟨   ∘ᵐ-congˡ R.barrier
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                          ∙ ∘ᵐ-identityʳ _
                        ,   ∘ᵐ-congˡ (  ∘ᵐ-identityˡ _
                                      ∙ ∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN)))
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                          ∙ str-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) gu fstᵐ
                              (⟨⟩ᵐ-fstᵐ _ _) ⟩ᵐ-cong))
  where
    r  = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    gu = ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ rel ∘ᵐ var-proj x ⟩ᵐ

    module R = Reindex (cong-⟨⟩-ren (wk-ren {Δ = Γ} {A = A}))
                       (⟨⊤⟩-η ∘ᵐ fstᵐ) (wk-free {Γ} {A}) H pH uH

-- `handle-delay`: the handled computation's `delay` becomes a `delay` of the
-- handled computation.

sound-handle-delay : ∀ {Γ A B τ ε ε'}
  → (M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
  → (H : (op : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ (of-natᵉ τ ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
  → Soundᶜ== (handle-delay M H N)
sound-handle-delay {Γ} {A} {B} {τ} {ε} {ε'} M H N (pM , pN , pH , uH) pR =
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , str-delay τ (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) ⟩ᵐ-cong)
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
                                          (∘ᵐ-congˡ (eq-ren-grade (trans map-·ᵉ
                                            (cong (_·ᵣ mapᵉ ε) map-of-natᵉ))))
                                          ≈ᵐ-refl)))) ⟩ᵐ-cong)
                      ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-refl , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong
                                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
                      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                      ∙ ∘ᵐ-congˡ (≈ᵐ-sym (R.alg-nat R.pHᵣ R.uHᵣ))))))
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst e (delay τ (handle M `with R.Hᵣ `in (C-rename r N))))
                pR (ε-substᴾ e _ pRc)
            ∙ sound-ε-subst e (delay τ (handle M `with R.Hᵣ `in (C-rename r N))) pRc)
  where
    e   = sym (·ₑ-assoc (of-natᵉ τ) ε ε')
    r   = cong-∷-ren (eq-ren (cong (Γ ⟨_⟩)
                               (trans map-·ᵉ (cong (_·ᵣ mapᵉ ε) map-of-natᵉ)))
                      ∘ʳ ⟨⟩-μ-ren)

    module R = Reindex (⟨⟩-≤-ren (≾-⊤ᵣ _) ∘ʳ ⟨⟩-μ-ren)
                       (⟨⟩-≤ (≾-⊤ᵣ (of-natʳ τ))) (barrier-μ (≾-⊤ᵣ _)) H pH uH

    pRc = pM , renᶜ r N pN , R.pHᵣ , R.uHᵣ
