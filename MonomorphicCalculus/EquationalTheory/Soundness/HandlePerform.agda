-------------------------------------------------------------------------
-- Soundness of the `handle-perform` equation.                         --
-- Handling an operation applies the matching clause, with the rest of --
-- the handled computation boxed up as the clause's continuation. The  --
-- inner handle's transport across the arity binder is                 --
-- `handle-op-cont`, shared verbatim with operational preservation.    --
-------------------------------------------------------------------------

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

module MonomorphicCalculus.EquationalTheory.Soundness.HandlePerform
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

open import MonomorphicCalculus.Syntax.Types           S
open import MonomorphicCalculus.Syntax.Contexts        S
open import MonomorphicCalculus.Syntax.Terms           S
open import MonomorphicCalculus.Syntax.Renaming        S
open import MonomorphicCalculus.Syntax.Renaming.Action S using (V-rename; C-rename; var-rename)
open import MonomorphicCalculus.Syntax.Substitution    S

open Category Cat
open Future Fut
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-idᵐ; ⟨⟩-congᶠ; μ; ⟨⟩-≤-irr)
open Adjunction Adj using (η⊣; ε⊣; η⊣-nat; η⊣-monoidal)
open GroundTypes GTy
open GroundEternal GE using (×-eternalᵒ; ×-eternalᵒ-extᵉ)
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η)

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.EquationalTheory.EquationalTheory S

open import MonomorphicCalculus.EquationalTheory.Soundness.Base S Cat Fut Pst Adj GTy Mon GE
       using (⟦⟧ᶜᵗ-irr; ⟦⟧ᵛᵗ-irr; Soundᶜ==)
open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE
       using (box-split; η⊣-⟨⟩)
open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.Handle S Cat Fut Pst Adj GTy Mon GE
       using (op-pair; op-env; str-op; str-op-box; gty-cancelᵛ; arity-box; cont-collapse)
open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation.HandleOpCont S Cat Fut Pst Adj GTy Mon GE
       using (handle-op-cont)
       renaming (H' to H'ᶜ; pH' to pH'ᶜ; uH' to uH'ᶜ)

private
  infixr 3 _∙_
  _∙_ : ∀ {A B} {f g h : A →ᵐ B} → f ≈ᵐ g → g ≈ᵐ h → f ≈ᵐ h
  _∙_ = ≈ᵐ-trans

  -- `handle M `with H `in N`, at the context read off the clause family `H`
  handleᴴ : ∀ {Γ A B ε ε'}
          → ((op : Op) → (ε'' : E)
               → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                    ∷ [ ∣ op-grade op ∣ᵉ ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                 ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
          → Γ ⊢C⦂ A ‼ ε → Γ ⟨ ∣ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε' → Γ ⊢C⦂ B ‼ (ε ·ₑ ε')
  handleᴴ H M N = handle M `with H `in N

  -- The reduct of `handle-perform` is the clause applied to the boxed
  -- continuation. The equation fixes the reduct's subterms, so that they are
  -- the rule's own terms; the continuation's body `M` is `M'` as a term (`q`),
  -- and its denotation is taken at the context `Δ` of `M'`.
  handle-perform-rhs : ∀ {Γ ρ A₀ Δ C B ε₁ ε₀} {L : Γ ⊢C⦂ B ‼ ε₀}
      {M : Γ ⟨ ρ ⟩ ∷ A₀ ⊢C⦂ C} {K : Γ ∷ [ ρ ] (A₀ ⇒ C) ⊢C⦂ B ‼ ε₁}
    → (e : ε₁ ≃ₑ ε₀)
    → Γ ⊢C⦂ L == ε-≃ e (box ρ (lam M) K)
    → (p : Paramᶜ (ε-≃ e (box ρ (lam M) K))) → (pK : Paramᶜ K)
    → (M' : Δ ⊢C⦂ C) → (q : _≡_ {A = Σ Ctx (_⊢C⦂ C)} (Δ , M') (Γ ⟨ ρ ⟩ ∷ A₀ , M))
    → (pM' : Paramᶜ M') → {f : ⟦ Δ ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ}
    → ⟦ M' ⟧ᶜᵗ pM' ≈ᵐ f
    → ⟦ ε-≃ e (box ρ (lam M) K) ⟧ᶜᵗ p
    ≈ᵐ T-≤ (proj₁ e)
         ∘ᵐ ⟦ K ⟧ᶜᵗ pK
         ∘ᵐ ⟨ idᵐ , [ ρ ]ᶠ (curryᵐ (subst (λ Δ → ⟦ Δ ⟧ᶜᵗˣ →ᵐ ⟦ C ⟧ᶜ) (cong proj₁ q) f))
                    ∘ᵐ η⊣ ⟩ᵐ
  handle-perform-rhs {ρ = ρ} {M = M} {K} e _ p pK .M refl pM' eq =
      ⟦⟧ᶜᵗ-irr (ε-≃ e (box ρ (lam M) K)) p (pM' , pK)
    ∙ sound-ε-≃ e (box ρ (lam M) K) (pM' , pK)
    ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong eq)) ⟩ᵐ-cong)

sound-handle-perform : ∀ {Γ A B ε ε' op}
  → (V : Γ ⊢V⦂ type-of-gtype (param op))
  → (M : Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
  → (H : (op' : Op) → (ε'' : E)
       → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
            ∷ [ ∣ op-grade op' ∣ᵉ ] (type-of-gtype (arity op') ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op' ·ₑ ε''))
  → (N : Γ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩ ∷ A ⊢C⦂ B ‼ ε')
  → Soundᶜ== (handle-perform V M H N)
sound-handle-perform {Γ} {A} {B} {ε} {ε'} {op} V M H N
                     ((pV , pM) , pN , pH , uH) pR = assembly
  where
    ren : Ren [] ((Γ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ type-of-gtype (arity op)) ⟨ ∣ ε ∣ᵉ ⟩)
                 (Γ ⟨ ∣ op-grade op ·ₑ ε ∣ᵉ ⟩)
    ren = (⟨⟩-≤-ren (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≃ᵣ⇒≿ᵣ map-·ᵉ) ∘ᵐ μ ∘ᵐ ⟨ ∣ ε ∣ᵉ ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (⟨⟩-≤-irr _ _)) ∙ ∘ᵐ-assoc _ _ _

    Vp = subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)

    e = ≃ₑ-sym (·ₑ-assoc (op-grade op) ε ε')

    -- the reduct's clause, with its certificate
    Cren = cong-∷-ren (cong-∷-ren barrier-ren)
    CL   = C-rename Cren (H op (ε ·ₑ ε'))
    pCL  = renᶜ Cren (H op (ε ·ₑ ε')) (pH op (ε ·ₑ ε'))

    -- the clause, contracted and substituted, is the clause at the empty
    -- extension applied to the eternal projection and the operation's value
    rhs-left =
        ∘ᵐ-congˡ (  C-subst-nat CL (split-∷ split-[]) V pCL pV
                  ∙ ∘ᵐ-congˡ (C-rename-nat Cren (H op (ε ·ₑ ε'))
                                (pH op (ε ·ₑ ε'))))
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
    -- (`arity-box`)
    boxeq =
        ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (arity-box (ty-gty (arity op)) _ _ _))

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
          ∙ ⟨   ∘ᵐ-congˡ (Eternalᵒ.necᵉ-mate (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat ⟨⊤⟩-η))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (η⊣-⟨⟩ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (cont-collapse _ _ _))

    assembly =
        handle-in-β (perform op V M) H N (pV , pM) pN pH uH
      ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
                  , str-op op (ty-gty (arity op)) Vp (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
                      ⟦ ren ⟧ʳ ern ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
                  ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-opᵀ op (⟨⊤⟩-eternalᵒ ⟦ Γ ⟧ᶜᵗˣ) (⟦_⟧ʰᵗ {Γ} H pH uH))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (
            ⟨⟩ᵐ-∘ _ _ _
          ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
            , ⟨⟩ᵐ-∘ _ _ _
              ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _
                , boxpart ⟩ᵐ-cong ⟩ᵐ-cong))
      -- the inner handle's fold is transported to the ambient barrier
      -- (`handle-op-cont`, shared with operational preservation)
      ∙ ≈ᵐ-sym (  handle-perform-rhs e (handle-perform V M H N) pR
                    (subᶜ CL (split-∷ split-[]) V pCL pV)
                    (handleᴴ (H'ᶜ H M N ren pM pN pH uH) M (C-rename (cong-∷-ren ren) N))
                    refl
                    (  pM , renᶜ (cong-∷-ren ren) N pN
                     , pH'ᶜ H M N ren pM pN pH uH , uH'ᶜ H M N ren pM pN pH uH)
                    (handle-op-cont H M N ren pM pN pH uH)
                ∙ ∘ᵐ-congʳ rhs-inner)
