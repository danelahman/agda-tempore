------------------------------------------------------------------------
-- Soundness of the effect-handling equations.                          --
--                                                                    --
-- Each is the corresponding `T-alg-of-handlerᵀ-*` law of the model,      --
-- with the handled computation's own former unfolded first. The shape   --
-- is the sequencing group's: `handle M `with H `in N` denotes            --
-- `T-alg-of-handlerᵀ … ∘ᵐ ⟨ projᴱ Γ , Tᶠ ⟦N⟧ ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦M⟧ ⟩ ⟩`, --
-- so the sub-computation sits in exactly the position `⨟` puts it and    --
-- the same strength laws apply.                                        --
--                                                                    --
-- `handle-return`: `strᵀ-ηᵀ` then `ηᵀ`-naturality expose the `ηᵀ` that    --
-- `T-alg-of-handlerᵀ-ηᵀ` consumes, leaving the continuation applied to   --
-- the transposed environment — which is what the right-hand side's       --
-- `⟨⟩-η-ren` and substitution build (as in `sound-seq-return`).          --
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
open import Relation.Nullary using (¬_; yes; no)

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
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤)
open Adjunction Adj using (η⊣; ε⊣)
open GroundTypes GTy
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

open import DenotationalSemantics.Soundness.Preservation.Unbox S Cat Fut Pst Adj GTy Mon GE
       using (unbox-def)

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
open import EquationalTheory.Soundness.Seq S Cat Fut Pst Adj GTy Mon GE
       using (εᵇ-η⊣-u; str-extend)

sound-handle-return : ∀ {Γ A B ε}
  → (V : Γ ⊢V⦂ A)
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ uₑ ⟩ ∷ A ⊢C⦂ B ‼ ε)
  → Soundᶜ== (handle-return V H N)
sound-handle-return {Γ} {A} {B} {ε} V H N (pV , pN , pH , uH , cH) pR =
    -- expose the `ηᵀ` the handler's algebra law consumes: the strength's
    -- unit law, then `ηᵀ`-naturality past the continuation
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   ∘ᵐ-congʳ (  ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                                ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
                            ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                            ∙ ∘ᵐ-congˡ strᵀ-ηᵀ
                            ∙ ∘ᵐ-assoc _ _ _)
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ηᵀ-nat _))
                ∙ ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong)
    -- and hand it to `T-alg-of-handlerᵀ-ηᵀ`, which returns the leaf
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (  mapˣᵐ-∘⟨⟩ _ _ _ _
                      ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-ηᵀ (⟦ Γ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ} H pH uH))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
    -- the environment the continuation receives is the transposed one
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                        ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ εᵇ-η⊣-u {⟦ Γ ⟧ᶜᵗˣ} map-uᵉ
                          , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
    -- which is what the right-hand side's renaming and substitution build
  ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (ε-subst e ((C-rename r N) [ Hd ↦ V ]c))
                pR (ε-substᴾ e _ pRc)
            ∙ sound-ε-subst e ((C-rename r N) [ Hd ↦ V ]c) pRc
            ∙ ∘ᵐ-congʳ (  C-subst-nat (C-rename r N) Hd V (renᶜ r N pN) pV
                        ∙ ∘ᵐ-congˡ (C-rename-nat r N pN)
                        ∙ ∘ᵐ-assoc _ _ _
                        ∙ ∘ᵐ-congʳ (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                    ∙ ⟨ ∘ᵐ-identityʳ _
                                        ∙ ∘ᵐ-congˡ (eq-ren-grade {Γ} map-uᵉ)
                                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  where
    e   = sym (·ₑ-identityˡ ε)
    r   = cong-∷-ren (⟨⟩-η-ren ∘ʳ eq-ren (cong (Γ ⟨_⟩) map-uᵉ))
    pRc = subᶜ (C-rename r N) Hd V (renᶜ r N pN) pV

-- `handle-box`: a `box` binder commutes with handling. The binder denotes an
-- environment extension `g` undone by `fstᵐ`, so the handled computation and
-- the continuation move by `str-extend`; the handler is untouched because
-- `(Γ ∷ [ ρ ] A) ᴱ = Γ ᴱ` (a box type is never eternal), which also makes
-- `projᴱ` reduce to `projᴱ Γ ∘ᵐ fstᵐ`.

sound-handle-box : ∀ {Γ A B C ρ ε ε'}
  → (V : Γ ⟨ ρ ⟩ ⊢V⦂ A)
  → (M : Γ ∷ [ ρ ] A ⊢C⦂ B ‼ ε)
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
         ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
  → Soundᶜ== (handle-box V M H N)
sound-handle-box {Γ} {A} {B} {C} {ρ} V M H N ((pV , pM) , pN , pH , uH , cH) pR =
  ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (box V (handle M `with H `in (C-rename r N))) pR
              (pV , (pM , renᶜ r N pN , pH , uH , cH))
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                      ∙ ⟨   ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                          ∙ ∘ᵐ-identityʳ _
                        ,   ∘ᵐ-congˡ (∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN)))
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                          ∙ str-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) g fstᵐ
                              (⟨⟩ᵐ-fstᵐ _ _) ⟩ᵐ-cong))
  where
    r = cong-∷-ren (cong-⟨⟩-ren wk-ren)
    g = ⟨ idᵐ , [ ρ ]ᶠ (⟦ V ⟧ᵛᵗ pV) ∘ᵐ η⊣ ⟩ᵐ

-- `handle-unbox`: the same for an `unbox` binder, except that `A` may be
-- eternal, so the eternal skeleton really does grow: `(Γ ∷ A) ᴱ` is `Γ ᴱ ∷ A`
-- or `Γ ᴱ`. The handler is therefore reindexed along `ren-ᴱ-∷ A`, and
-- `T-alg-of-handlerᵀ-natᴾ` transports the fold along it — its two premises
-- being `restrict-ren-necᵉ` (the necessitation commutes) and `clause-nat`
-- (the clauses commute, `adapt-comm` moving the reindexing past the
-- ground-type adapters). `ren-ᴱ-∷ A` *is* `restrict-ren wk-ren`, which is what
-- lets those two be reused verbatim.

private
  ren-ᴱ-∷≡ : ∀ {Γ} → (A : VType) → ren-ᴱ-∷ {Γ} A ≡ restrict-ren (wk-ren {Γ} {A})
  ren-ᴱ-∷≡ A with eternal? A
  ... | yes _ = refl
  ... | no  _ = refl

  -- the ground-type adapter commutes with reindexing the eternal parameter
  adapt-comm : ∀ {D D' P Q R S} → (g : D →ᵐ D') → (p : Q →ᵐ P) → (a : S →ᵐ R)
             → mapˣᵐ (mapˣᵐ g idᵐ) idᵐ ∘ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D}) p) a ∘ᵐ ×ᵐ-assoc⁻¹)
             ≈ᵐ (mapˣᵐ (mapˣᵐ (idᵐ {D'}) p) a ∘ᵐ ×ᵐ-assoc⁻¹) ∘ᵐ mapˣᵐ g idᵐ
  adapt-comm g p a =
      ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
    ∙ ∘ᵐ-congˡ (  mapˣᵐ-∘ _ _ _ _
                ∙ mapˣᵐ-cong (  mapˣᵐ-∘ _ _ _ _
                              ∙ mapˣᵐ-cong (∘ᵐ-identityʳ _) (∘ᵐ-identityˡ _))
                             (∘ᵐ-identityˡ _))
    ∙ ≈ᵐ-sym (  ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (×ᵐ-assoc⁻¹-natˡ g)
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (  mapˣᵐ-∘ _ _ _ _
                          ∙ mapˣᵐ-cong (  mapˣᵐ-∘ _ _ _ _
                                        ∙ mapˣᵐ-cong (∘ᵐ-identityˡ _) (∘ᵐ-identityʳ _))
                                       (∘ᵐ-identityʳ _)))

sound-handle-unbox : ∀ {Γ A B C ρ Δ ε ε'}
  → (w : Ren (Δ ⟨ ρ ⟩) Γ)
  → (V : Δ ⊢V⦂ [ ρ ] A)
  → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
  → (H : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → Γ ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
         ⊢C⦂ C ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ B ⊢C⦂ C ‼ ε')
  → Soundᶜ== (handle-unbox w V M H N)
sound-handle-unbox {Γ} {A} {B} {C} {ρ} {Δ} {ε} {ε'} w V M H N
                   ((pV , pM) , pN , pH , uH , cH)
                   (pV₂ , pM₂ , pN₂ , pH₂ , uH₂ , cH₂) =
  ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr (unbox w V (handle M `with H' `in (C-rename r N)))
              (pV₂ , pM₂ , pN₂ , pH₂ , uH₂ , cH₂)
              (pV , (pM , renᶜ r N pN , pH₂ , uH₂ , cH₂))
          ∙ unbox-def w V (handle M `with H' `in (C-rename r N)) pV
              (pM , renᶜ r N pN , pH₂ , uH₂ , cH₂)
            -- transport the fold along the eternal-skeleton renaming
          ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ alg-nat)
          ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (mapˣᵐ-∘⟨⟩ _ _ _ _)
                      ∙ ⟨⟩ᵐ-∘ _ _ _
                        -- the eternal part is untouched by the binder …
                      ∙ ⟨   ∘ᵐ-congˡ (≈ᵐ-sym projᴱ-wk)
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                          ∙ ∘ᵐ-identityʳ _
                        -- … and the continuation moves as in `handle-box`
                        ,   ∘ᵐ-congˡ (  ∘ᵐ-identityˡ _
                                      ∙ ∘ᵐ-congˡ (T-congᶠ (C-rename-nat r N pN)))
                          ∙ ∘ᵐ-assoc _ _ _
                          ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
                          ∙ str-extend (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) gu fstᵐ
                              (⟨⟩ᵐ-fstᵐ _ _) ⟩ᵐ-cong))
  where
    r  = cong-∷-ren (cong-⟨⟩-ren wk-ren)

    H' : (op : Op) → (ε'' : E) → (Γ' : Ctx)
       → (Γ ∷ A) ᴱ ++ᶜ Γ' ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ C ‼ ε'')
         ⊢C⦂ C ‼ (op-grade op ·ₑ ε'')
    H' op' ε'' Γ' = C-rename (cong-ren (ren-ᴱ-∷ {Γ} A)) (H op' ε'' Γ')

    gu = ⟨ idᵐ , ε⊣ ∘ᵐ ⟨⟩-≤ (proj₂ (proj₂ (unbox⇒var w V)))
                    ∘ᵐ var-proj (proj₁ (proj₂ (unbox⇒var w V))) ⟩ᵐ

    f : ⟦ (Γ ∷ A) ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ ᴱ ⟧ᶜᵗˣ
    f = ⟦ ren-ᴱ-∷ {Γ} A ⟧ʳ

    necᵉ-comm : ∀ {ρ₀}
              → [ ρ₀ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ ∷ A ⟧ᴱ-Eternalᵒ) {ρ₀}
              ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ₀} ∘ᵐ f
    necᵉ-comm {ρ₀} =
      subst (λ z → [ ρ₀ ]ᶠ ⟦ z ⟧ʳ ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ ∷ A ⟧ᴱ-Eternalᵒ) {ρ₀}
                 ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ ⟧ᴱ-Eternalᵒ) {ρ₀} ∘ᵐ ⟦ z ⟧ʳ)
            (sym (ren-ᴱ-∷≡ {Γ} A))
            (restrict-ren-necᵉ (wk-ren {Γ} {A}))

    projᴱ-wk : projᴱ Γ ∘ᵐ fstᵐ ≈ᵐ f ∘ᵐ projᴱ (Γ ∷ A)
    projᴱ-wk =
      subst (λ z → projᴱ Γ ∘ᵐ ⟦ wk-ren {Γ} {A} ⟧ʳ ≈ᵐ ⟦ z ⟧ʳ ∘ᵐ projᴱ (Γ ∷ A))
            (sym (ren-ᴱ-∷≡ {Γ} A))
            (projᴱ-nat (wk-ren {Γ} {A}))

    clause-nat : ∀ op ε''
               → clauseᵀ (⟦_⟧ʰᵗ {Γ ∷ A} H' pH₂ uH₂) op ε''
               ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
    clause-nat op ε'' =
        ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (H' op ε'' []) (pH₂ op ε'' [])
                      (renᶜ (cong-ren (ren-ᴱ-∷ {Γ} A)) (H op ε'' []) (pH op ε'' []))
                  ∙ C-rename-nat (cong-ren (ren-ᴱ-∷ {Γ} A)) (H op ε'' []) (pH op ε'' []))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (adapt-comm _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    alg-nat = T-alg-of-handlerᵀ-natᴾ (⟦ Γ ⟧ᴱ-Eternalᵒ) (⟦ Γ ∷ A ⟧ᴱ-Eternalᵒ)
                f necᵉ-comm (⟦_⟧ʰᵗ {Γ} H pH uH) (⟦_⟧ʰᵗ {Γ ∷ A} H' pH₂ uH₂)
                clause-nat
