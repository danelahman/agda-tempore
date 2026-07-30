------------------------------------------------------------------------
-- Soundness of the `handle-perform` equation.                          --
--                                                                    --
-- Handling an operation applies the matching clause, with the rest of  --
-- the handled computation boxed up as the clause's continuation. The   --
-- proof is the parametric generalisation of the operational            --
-- `sound-HANDLE-OP`: the eternal parameter is threaded live and carried --
-- under the operation's box by `necᵉ`, rather than collapsed to the     --
-- terminal object as in a closed runtime configuration.                --
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
open import Syntax.RenActions    S using (V-rename; C-rename; var-rename)
open import Syntax.Substitutions S

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ; μ)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open GroundEternal GE using (×-eternalᵒ; ×-eternalᵒ-extᵉ)
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

open import EquationalTheory.EquationalTheory S

open import EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
       using (⟦⟧ᶜᵗ-irr; ⟦⟧ᵛᵗ-irr; Soundᶜ==)
open import OperationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE
       using (box-split; η⊣-⟨⟩)
open import OperationalSemantics.Soundness.Preservation.Handle S Cat Fut Pst Adj GTy Mon GE
       using (op-pair; op-env; str-op; str-op-box; gty-cancelᵛ; arity-box; cont-collapse)
open import OperationalSemantics.Soundness.Preservation.HandleOpCont S Cat Fut Pst Adj GTy Mon GE
       using (ren-ᴱ-∷≡restrict)

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

-- ───────────────────────────────────────────────────────────────────────────
-- Transporting the fold along an eternal-skeleton extension, with a live
-- parameter.
--
-- `HandleOpCont.handle-op-cont` does this only at a runtime configuration
-- (`Γ ᴱ ≡ []`), where the parameter collapses by terminality. Here the
-- parameter is carried, so the reconciliation is `T-alg-of-handlerᵀ-natᴾ`
-- along `ren-ᴱ-∷ A₀` — as in `sound-handle-unbox`, but over an arbitrary base.
-- ───────────────────────────────────────────────────────────────────────────

module _ {Γ₀ : Ctx} {B : VType} (A₀ : VType)
         (H : (op : Op) → (ε'' : E)
            → Γ₀ ᴱ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
         (pH : ∀ op ε'' → Paramᶜ (H op ε''))
         (uH : EffUniformʰ {Γ₀} H pH)
       where

  -- the clauses reindexed to the extended eternal skeleton
  Hᴿ : (op : Op) → (ε'' : E)
     → (Γ₀ ∷ A₀) ᴱ ∷ type-of-gtype (param op)
          ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
       ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
  Hᴿ op ε'' = C-rename (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {Γ₀} A₀))) (H op ε'')

  fᴿ : ⟦ (Γ₀ ∷ A₀) ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ Γ₀ ᴱ ⟧ᶜᵗˣ
  fᴿ = ⟦ ren-ᴱ-∷ {Γ₀} A₀ ⟧ʳ

  -- `ren-ᴱ-∷ A₀` *is* `restrict-ren wk-ren`, so the two coherences transport
  necᵉ-commᴿ : ∀ {ρ₀}
             → [ ρ₀ ]ᶠ fᴿ ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ) {ρ₀}
             ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) {ρ₀} ∘ᵐ fᴿ
  necᵉ-commᴿ {ρ₀} =
    subst (λ z → [ ρ₀ ]ᶠ ⟦ z ⟧ʳ ∘ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ) {ρ₀}
               ≈ᵐ Eternalᵒ.necᵉ (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) {ρ₀} ∘ᵐ ⟦ z ⟧ʳ)
          (sym (ren-ᴱ-∷≡restrict {Γ₀} A₀))
          (restrict-ren-necᵉ (wk-ren {Δ = Γ₀} {A = A₀}))

  projᴱ-wkᴿ : projᴱ Γ₀ ∘ᵐ fstᵐ ≈ᵐ fᴿ ∘ᵐ projᴱ (Γ₀ ∷ A₀)
  projᴱ-wkᴿ =
    subst (λ z → projᴱ Γ₀ ∘ᵐ ⟦ wk-ren {Δ = Γ₀} {A = A₀} ⟧ʳ ≈ᵐ ⟦ z ⟧ʳ ∘ᵐ projᴱ (Γ₀ ∷ A₀))
          (sym (ren-ᴱ-∷≡restrict {Γ₀} A₀))
          (projᴱ-nat (wk-ren {Δ = Γ₀} {A = A₀}))

  module _ (pHᴿ : ∀ op ε'' → Paramᶜ (Hᴿ op ε''))
           (uHᴿ : EffUniformʰ {Γ₀ ∷ A₀} Hᴿ pHᴿ)
         where

    clause-natᴿ : ∀ op ε''
                → clauseᵀ (⟦_⟧ʰᵗ {Γ₀ ∷ A₀} Hᴿ pHᴿ uHᴿ) op ε''
                ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {Γ₀} H pH uH) op ε'' ∘ᵐ mapˣᵐ fᴿ idᵐ
    clause-natᴿ op ε'' =
        ∘ᵐ-congˡ (  ⟦⟧ᶜᵗ-irr (Hᴿ op ε'') (pHᴿ op ε'')
                      (renᶜ (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {Γ₀} A₀)))
                            (H op ε'') (pH op ε''))
                  ∙ C-rename-nat (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {Γ₀} A₀)))
                      (H op ε'') (pH op ε''))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (adapt-commute _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    alg-natᴿ : ∀ {ε ε'}
             → T-alg-of-handlerᵀ {_} {_} {ε} {ε'}
                 (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ₀ ∷ A₀} Hᴿ pHᴿ uHᴿ)
             ≈ᵐ T-alg-of-handlerᵀ {_} {_} {ε} {ε'}
                  (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ₀} H pH uH)
                ∘ᵐ mapˣᵐ fᴿ idᵐ
    alg-natᴿ =
      T-alg-of-handlerᵀ-natᴾ (⟦ Γ₀ ⟧ᴱ-Eternalᵒ) (⟦ Γ₀ ∷ A₀ ⟧ᴱ-Eternalᵒ)
        fᴿ necᵉ-commᴿ (⟦_⟧ʰᵗ {Γ₀} H pH uH) (⟦_⟧ʰᵗ {Γ₀ ∷ A₀} Hᴿ pHᴿ uHᴿ)
        clause-natᴿ


-- ───────────────────────────────────────────────────────────────────────────
-- The clause included into `Γ` is the clause reindexed by `projᴱ Γ`.
--
-- The fold's operation law returns `clauseᵀ h op _`, the clause read at its own
-- eternal skeleton; the equation's right-hand side uses the clause included
-- into `Γ` by `ᴱ-ren`, whose denotation is exactly `projᴱ Γ` (`ᴱ-ren-mor`).
-- ───────────────────────────────────────────────────────────────────────────

ᴱ-ren-clause : ∀ {Γ B}
  → (H : (op : Op) → (ε'' : E)
       → Γ ᴱ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
  → ∀ op ε''
  → ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'') ∘ᵐ mapˣᵐ (mapˣᵐ ⟦ ᴱ-ren Γ ⟧ʳ idᵐ) idᵐ
  ≈ᵐ ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'') ∘ᵐ mapˣᵐ (mapˣᵐ (projᴱ Γ) idᵐ) idᵐ
ᴱ-ren-clause {Γ} H pH op ε'' =
  ∘ᵐ-congʳ (mapˣᵐ-cong (mapˣᵐ-cong (ᴱ-ren-mor Γ) ≈ᵐ-refl) ≈ᵐ-refl)


-- ═══════════════════════════════════════════════════════════════════════════
-- THE AXIOM: handling an operation applies the matching clause, with the rest
-- of the handled computation boxed up as the clause's continuation.
-- ═══════════════════════════════════════════════════════════════════════════

sound-handle-perform : ∀ {Γ A B ε ε' op}
  → (V : Γ ⊢V⦂ type-of-gtype (param op))
  → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
  → (H : (op' : Op) → (ε'' : E)
       → Γ ᴱ ∷ type-of-gtype (param op')
            ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op' ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
  → Soundᶜ== (handle-perform V M H N)
sound-handle-perform {Γ} {A} {B} {ε} {ε'} {op} V M H N
                     ((pV , pM) , pN , pH , uH) pR = assembly
  where
    ren : Ren [] ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
                 (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
    ren = (eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade {Γ} map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

    Vp = subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)

    e = sym (·ₑ-assoc (op-grade op) ε ε')

    -- the reduct's pieces, with their certificates
    H' : (op' : Op) → (ε'' : E)
       → (Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ᴱ
           ∷ type-of-gtype (param op')
           ∷ [ mapᵉ (op-grade op') ] (type-of-gtype (arity op') ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'')
    H' op' ε'' =
      C-rename (cong-∷-ren (cong-∷-ren
                 (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op)))))
               (H op' ε'')

    pH' : ∀ op' ε'' → Paramᶜ (H' op' ε'')
    pH' op' ε'' =
      renᶜ (cong-∷-ren (cong-∷-ren
             (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op)))))
           (H op' ε'') (pH op' ε'')

    uH' : EffUniformʰ {Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)} H' pH'
    uH' = ren-clauses-uniform
            (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op))) H pH uH

    Cren = cong-∷-ren (cong-∷-ren (ᴱ-ren Γ))
    CL   = C-rename Cren (H op (ε ·ₑ ε'))
    pCL  = renᶜ Cren (H op (ε ·ₑ ε')) (pH op (ε ·ₑ ε'))

    pBody : Paramᶜ (handle M `with H' `in (C-rename (cong-∷-ren ren) N))
    pBody = pM , renᶜ (cong-∷-ren ren) N pN , pH' , uH'

    pBox : Paramᶜ (box (lam (handle M `with H' `in (C-rename (cong-∷-ren ren) N)))
                       (CL [ Tl-∷ Hd ↦ V ]c))
    pBox = pBody , subᶜ CL (Tl-∷ Hd) V pCL pV

    -- the clause, contracted and substituted, is the clause at the empty
    -- extension applied to the eternal projection and the operation's value
    rhs-left =
        ∘ᵐ-congˡ (  C-subst-nat CL (Tl-∷ Hd) V pCL pV
                  ∙ ∘ᵐ-congˡ (  C-rename-nat Cren (H op (ε ·ₑ ε'))
                                  (pH op (ε ·ₑ ε'))
                              ∙ ᴱ-ren-clause {Γ} {B} H pH op (ε ·ₑ ε')))
      ∙ ∘ᵐ-congˡ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (  ∘ᵐ-congˡ (  mapˣᵐ-∘ _ _ _ _
                              ∙ mapˣᵐ-cong (  mapˣᵐ-∘⟨⟩ _ _ _ _
                                            ∙ ⟨ ∘ᵐ-identityʳ _
                                              , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
                                           (∘ᵐ-identityˡ _))
                  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityʳ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)

    -- the boxed continuation on the reduct side: the arity coercions cancel
    -- (`arity-box`), the inner handle's fold is transported to the ambient
    -- eternal base (`alg-natᴿ`/`projᴱ-wkᴿ`), the sequel's renaming is `C-rename-nat`
    boxeq =
      -- merge the coercion into the box and cancel it against the arity subst
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (arity-box (ty-gty (arity op)) _ _ _))
      -- and what is left is the reduct's inner handle, once its fold is
      -- transported to the ambient eternal base
      ∙ ≈ᵐ-sym (∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (
            ∘ᵐ-congˡ (alg-natᴿ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                        (type-of-gtype (arity op)) H pH uH pH' uH')
          ∙ ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _)
          ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-sym (projᴱ-wkᴿ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                                 (type-of-gtype (arity op)) H pH uH)
                      , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
          ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                      , ∘ᵐ-congˡ (T-congᶠ
                          (C-rename-nat (cong-∷-ren ren) N pN)) ⟩ᵐ-cong)))))

    rhs-inner =
        rhs-left
      ∙ ≈ᵐ-sym (
            ∘ᵐ-assoc _ _ _
          ∙ ∘ᵐ-congʳ (
                ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                          ∙ ⟨   ⟨⟩ᵐ-∘ _ _ _
                              ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
                                ,   ∘ᵐ-assoc _ _ _
                                  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                                  ∙ ⟨⟩ᵐ-fstᵐ _ _ ⟩ᵐ-cong
                            ,   ∘ᵐ-assoc _ _ _
                              ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
                              ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
              ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
              ∙ ⟨   mapˣᵐ-∘⟨⟩ _ _ _ _
                  ∙ ⟨ ∘ᵐ-identityˡ _ , gty-cancelᵛ (ty-gty (param op)) _ ⟩ᵐ-cong
                , boxeq ⟩ᵐ-cong))

    -- the operation's boxed continuation: the eternal parameter is carried
    -- under the box by `necᵉ` (its mate `η⊣`), pairs up with the continuation
    -- by `η⊣-⟨⟩`, and the fold is applied inside by `cont-collapse`
    boxpart =
        ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (
            ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
            , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            mapˣᵐ-∘⟨⟩ _ _ _ _
          ∙ ⟨   ∘ᵐ-congˡ (Eternalᵒ.necᵉ-mate (⟦ Γ ⟧ᴱ-Eternalᵒ))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (projᴱ Γ)))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (η⊣-⟨⟩ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (cont-collapse _ _ _))

    assembly =
      -- `str-op` moves the sequel `N` into the operation's boxed continuation
        ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                  , str-op op (ty-gty (arity op)) Vp (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
                      ⟦ ren ⟧ʳ ern ⟩ᵐ-cong)
      -- re-form `mapˣᵐ idᵐ (opᵀ op)` and apply the fold's operation law
      ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-opᵀ op (⟦ Γ ⟧ᴱ-Eternalᵒ) (⟦_⟧ʰᵗ {Γ} H pH uH))
      -- the law's reshuffle returns the eternal and operation parameters
      -- unchanged; the continuation carries the rest
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
            , ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _
                , boxpart ⟩ᵐ-cong ⟩ᵐ-cong))
      -- what remains is the reduct: the clause at `Γ`, applied to the
      -- parameter and to the boxed continuation the `box` allocates
      ∙ ≈ᵐ-sym (  ⟦⟧ᶜᵗ-irr
                    (ε-subst e
                      (box (lam (handle M `with H' `in (C-rename (cong-∷-ren ren) N)))
                           (CL [ Tl-∷ Hd ↦ V ]c)))
                    pR (ε-substᴾ e _ pBox)
                ∙ sound-ε-subst e
                    (box (lam (handle M `with H' `in (C-rename (cong-∷-ren ren) N)))
                         (CL [ Tl-∷ Hd ↦ V ]c))
                    pBox
                ∙ ∘ᵐ-congʳ rhs-inner)
