{-# OPTIONS --lossy-unification #-}

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

module OperationalSemantics.Soundness.Preservation.Handle
         (S : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades S)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades S)) Fut Pst)
         (GTy : GroundTypes S Cat Fut)
         (Mon : Monad S Cat Fut Pst Adj GTy)
         (GE : GroundEternal S Cat Fut Pst Adj GTy)
       where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

open import Syntax.Types     S
open import Syntax.Contexts  S
open import Syntax.Language  S
open import Syntax.Renamings S
open import Syntax.RenActions S using (V-rename; C-rename; var-rename)
open import Syntax.Substitutions S
open import Syntax.Substitutions.Subsumption S

open import OperationalSemantics.State S
open import OperationalSemantics.PreservationTheorem S

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ; []-congᶠ; []-idᵐ; []-∘ᵐ; []-≤; []-≤-refl; []-≤-nat;
                       []-ε-nat; []-ε∘ηᵘ≡id; ηᵘ; δ; []-δ-nat; []-monoidal; []-≤-trans;
                       []-monoidal-nat; []-monoidal-fstᵐ; []-monoidal-sndᵐ; []-monoidal-η;
                       []-𝟙-unique) renaming (ε to εᵇ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ; η; μ; ⟨⟩-≤; ⟨⟩-∘ᵐ; ⟨⟩-congᶠ; ⟨⟩-η-nat; ⟨⟩-μ-nat;
                     ⟨⟩-≤-nat; ⟨⟩-≤-irr; ⟨⟩-≤-refl; ⟨⟩-≤-trans; μ-≤ˡ; μ-≤ʳ;
                     ⟨⟩-μ∘Tη≡id; ⟨⟩-μ∘η≡id)
open Adjunction Adj using (η⊣; η⊣-nat; η⊣-u; η⊣-≤; η⊣-δ; η⊣-monoidal;
                           ε⊣; ε⊣-nat; triangleˡ)
open GroundTypes GTy using (⟦_⟧ᵍ)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Variables S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Contexts S Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.Renaming S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.RenamingCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.SubstitutionCoherence S Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State S Cat Fut Pst Adj GTy Mon GE

open import DenotationalSemantics.Model.Modality.Eternal
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj
       using (Eternalᵒ; ⟨⊤⟩-eternalᵒ; ⟨⊤⟩-η; ⟨⊤⟩-μ; ⟨⊤⟩-η-nat; ⟨⊤⟩-μ∘Tη≡id; ⟨⊤⟩-μ-nat;
              free-extᵉ-nat; free-necᵉ-nat; barrier-μ; barrier-lock)
open import OperationalSemantics.Soundness.Preservation.HandleOpCont S Cat Fut Pst Adj GTy Mon GE
  using (handle-op-cont)
open import OperationalSemantics.Soundness.Preservation.HandleOpClause S Cat Fut Pst Adj GTy Mon GE
  using (clause-sound)

open import DenotationalSemantics.Interpretation.Subtyping S Cat Fut Pst Adj GTy Mon

open import OperationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE public

-- A handler commutes with a step transition: `stepᵀ r` is `ηᵀ` except for
-- `DELAY`'s tick, and a reduction step never performs an operation. This
-- fails for a general tree, where `alg ∘ᵐ μᵀ ≈ᵐ μᵀ ∘ᵐ Tᶠ alg` does not hold.

-- The algebra commutes with a grade transport (derivable from `alg-≤`).

alg-ε-subst : ∀ {B P ε₂ ε₁' ε₂'}
            → (alg : ∀ {ε} → P ×ᵐ Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
            → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                     → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
                     ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
            → (e : ε₁' ≡ ε₂')
            → alg {ε₂'} ∘ᵐ mapˣᵐ idᵐ (ε-substᵀ e)
            ≈ᵐ ε-substᵀ (cong (_·ₑ ε₂) e) ∘ᵐ alg {ε₁'}
alg-ε-subst alg alg-≤ e =
    ∘ᵐ-congʳ (mapˣᵐ-cong ≈ᵐ-refl (T-≤-≡ e))
  ∙ alg-≤ (≾ₑ-reflexive e)
  ∙ ∘ᵐ-congˡ (T-≤-irr _ (≾ₑ-reflexive (cong (_·ₑ _) e)))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-≤-≡ (cong (_·ₑ _) e)))

-- The `ηᵀ` case: a step that performs nothing. Both sides collapse by the
-- monad's left-unit law, and the algebra passes the returned value through.

alg-ηᵀ : ∀ {B Y P ε ε₂}
       → (alg : ∀ {ε'} → P ×ᵐ Tᵒ (Tᵒ B ε₂) ε' →ᵐ Tᵒ B (ε' ·ₑ ε₂))
       → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
                ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
       → (pv : Y →ᵐ P)
       → (f : Y →ᵐ Tᵒ (Tᵒ B ε₂) ε)
       → alg {uₑ ·ₑ ε} ∘ᵐ ⟨ pv , μᵀ {Tᵒ B ε₂} {uₑ} {ε} ∘ᵐ Tᶠ f ∘ᵐ ηᵀ ⟩ᵐ
       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc uₑ ε ε₂))
           ∘ᵐ μᵀ {B} {uₑ} {ε ·ₑ ε₂} ∘ᵐ Tᶠ (alg {ε} ∘ᵐ ⟨ pv , f ⟩ᵐ) ∘ᵐ ηᵀ
alg-ηᵀ {ε = ε} {ε₂ = ε₂} alg alg-≤ pv f =
  -- pull `ηᵀ` to the front, then the unit law collapses `μᵀ ∘ ηᵀ`
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              ,   ∘ᵐ-congʳ (≈ᵐ-sym (ηᵀ-nat f))
                ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                ∙ ∘ᵐ-congˡ T-μ∘η≡id ⟩ᵐ-cong)
  -- the algebra passes the transport through
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (alg-ε-subst alg alg-≤ (sym (·ₑ-identityˡ ε)))
  ∙ ∘ᵐ-assoc _ _ _
  -- and the two accumulated transports agree (`uip`), so the same chain
  -- rebuilds the right-hand side
  ∙ ∘ᵐ-congˡ (≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ε-substᵀ-trans _ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym T-μ∘η≡id))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (ηᵀ-nat (alg ∘ᵐ ⟨ pv , f ⟩ᵐ)))

-- The eternal parameter carried across a step transition. Only `DELAY` extends
-- the history, and there the parameter passes under the new lock.

step-pv : ∀ {ε₁ ε₃ A A₀ P} {S S' : 𝕊 []}
        → {M : toCtx S ⊢C⦂ A ‼ ε₁} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε₃}
        → (bc : Eternalᵒ P) → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
        → (⟦ hist S ⟧ᶜᵗˣ →ᵐ P) → (⟦ hist S' ⟧ᶜᵗˣ →ᵐ P)
step-pv bc APP               pv = pv
step-pv bc MATCH             pv = pv
step-pv bc IF-TRUE           pv = pv
step-pv bc IF-FALSE          pv = pv
step-pv bc SEQ-RET           pv = pv
step-pv bc SEQ-OP            pv = pv
step-pv bc HANDLE-RET        pv = pv
step-pv bc HANDLE-OP         pv = pv
step-pv bc BOX               pv = pv
step-pv bc UNBOX             pv = pv
step-pv bc SUB-APP           pv = pv
step-pv bc SUB-IF            pv = pv
step-pv bc SUB               pv = pv
step-pv bc (SEQ-STEP r c)    pv = step-pv bc r pv
step-pv bc (HANDLE-STEP r c) pv = step-pv bc r pv
step-pv bc (DELAY {τ = τ})   pv = Eternalᵒ.extᵉ bc ∘ᵐ ⟨ of-natʳ τ ⟩ᶠ pv

-- The step transition commutes with the handler, by induction on the
-- reduction. Eleven rules transition by `ηᵀ` (`alg-ηᵀ`); `DELAY` ticks, and the
-- fold *re-delays*, carrying the parameter under the tick's box by `necᵉ`; the
-- two step rules inherit their transition from the sub-step.

alg-stepᵀ : ∀ {ε ε₂ ε₁' ε₃' A A₀ B P} {S S' : 𝕊 []}
          → {M : toCtx S ⊢C⦂ A ‼ ε₁'} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε₃'}
          → (bc : Eternalᵒ P)
          → (alg : ∀ {ε'} → P ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε' →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε' ·ₑ ε₂))
          → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                   → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q)
                   ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
          → (alg-delay : ∀ {ε'} → (τ : ℕ)
                       → alg {of-natᵉ τ ·ₑ ε'}
                           ∘ᵐ mapˣᵐ idᵐ (delayᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {ε'} τ)
                       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
                           ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (alg {ε'})
                           ∘ᵐ []-monoidal
                           ∘ᵐ mapˣᵐ (Eternalᵒ.necᵉ bc {of-natʳ τ}) idᵐ)
          → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
          → (pv : ⟦ hist S ⟧ᶜᵗˣ →ᵐ P)
          → (f : ⟦ hist S' ⟧ᶜᵗˣ →ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε)
          → alg {step-grade r ·ₑ ε}
              ∘ᵐ ⟨ pv , μᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {step-grade r} {ε} ∘ᵐ Tᶠ f ∘ᵐ stepᵀ r ⟩ᵐ
          ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (step-grade r) ε ε₂))
              ∘ᵐ μᵀ {⟦ B ⟧ᵛ} {step-grade r} {ε ·ₑ ε₂}
              ∘ᵐ Tᶠ (alg {ε} ∘ᵐ ⟨ step-pv bc r pv , f ⟩ᵐ) ∘ᵐ stepᵀ r
alg-stepᵀ bc alg alg-≤ alg-delay APP        pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay MATCH      pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay IF-TRUE    pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay IF-FALSE   pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay SEQ-RET    pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay SEQ-OP     pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay HANDLE-RET pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay HANDLE-OP  pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay BOX        pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay UNBOX      pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay SUB-APP    pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay SUB-IF     pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ bc alg alg-≤ alg-delay SUB        pv f = alg-ηᵀ alg alg-≤ pv f
alg-stepᵀ {B = B} bc alg alg-≤ alg-delay (SEQ-STEP r c) pv f =
  alg-stepᵀ {B = B} bc alg alg-≤ alg-delay r pv f
alg-stepᵀ {B = B} bc alg alg-≤ alg-delay (HANDLE-STEP r c) pv f =
  alg-stepᵀ {B = B} bc alg alg-≤ alg-delay r pv f
alg-stepᵀ {ε = ε} {ε₂ = ε₂} {B = B} bc alg alg-≤ alg-delay (DELAY {τ = τ}) pv f =
  -- Both sides reach the same normal form: the tick, with the *whole* bind
  -- carried under the box. `alg-ηᵀ` does the work there — under `[ of-natʳ τ ]`
  -- the step has become the trivial one, and the parameter has crossed the box
  -- as the lock's extraction.
  lhs ∙ ∘ᵐ-congˡ (≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip)) ∙ ≈ᵐ-sym rhs
  where
    pv' = Eternalᵒ.extᵉ bc {of-natʳ τ} ∘ᵐ ⟨ of-natʳ τ ⟩ᶠ pv

    -- the common normal form
    NF : _ →ᵐ _
    NF = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (μᵀ ∘ᵐ Tᶠ (alg {ε} ∘ᵐ ⟨ pv' , f ⟩ᵐ) ∘ᵐ ηᵀ) ∘ᵐ η⊣

    -- the tick is pulled out of the bind and everything collected under the box
    pre : μᵀ ∘ᵐ Tᶠ f ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
        ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) uₑ ε))
            ∘ᵐ ((delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ μᵀ)
                  ∘ᵐ ([ of-natʳ τ ]ᶠ (Tᶠ f ∘ᵐ ηᵀ) ∘ᵐ η⊣))
    pre =
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ f)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (delayᵀ-algebraicity τ)
      ∙ ∘ᵐ-assoc _ _ _

    -- the parameter crosses the tick's box as the lock's extraction, and pairs
    -- back up with the bind under one box (`necᵉ-mate`, `η⊣-⟨⟩`)
    cross : []-monoidal ∘ᵐ ⟨ Eternalᵒ.necᵉ bc {of-natʳ τ} ∘ᵐ pv
                           , [ of-natʳ τ ]ᶠ μᵀ
                               ∘ᵐ ([ of-natʳ τ ]ᶠ (Tᶠ f ∘ᵐ ηᵀ) ∘ᵐ η⊣) ⟩ᵐ
          ≈ᵐ [ of-natʳ τ ]ᶠ ⟨ pv' , μᵀ ∘ᵐ Tᶠ f ∘ᵐ ηᵀ ⟩ᵐ ∘ᵐ η⊣
    cross =
        ∘ᵐ-congʳ
          (⟨   ∘ᵐ-congˡ (Eternalᵒ.necᵉ-mate bc)
             ∙ ∘ᵐ-assoc _ _ _
             ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat pv))
             ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
             ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
           ,   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
             ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)) ⟩ᵐ-cong)
      ∙ η⊣-⟨⟩ _ _

    -- the source: pull the tick out, carry the parameter across, then `alg-ηᵀ`
    lhs : alg {of-natᵉ τ ·ₑ uₑ ·ₑ ε}
            ∘ᵐ ⟨ pv , μᵀ ∘ᵐ Tᶠ f ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣) ⟩ᵐ
        ≈ᵐ ε-substᵀ _ ∘ᵐ NF
    lhs =
        ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , pre ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (alg-ε-subst alg alg-≤ (sym (·ₑ-assoc (of-natᵉ τ) uₑ ε)))
      ∙ ∘ᵐ-assoc _ _ _
      -- re-form `mapˣᵐ idᵐ (delayᵀ τ)` and fire the fold's delay law
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ∘ᵐ-assoc _ _ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (alg-delay τ))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)
      -- the parameter and the bind meet under the tick's box
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ cross))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
      -- under the box the step has become the trivial one: `alg-ηᵀ` applies
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (alg-ηᵀ alg alg-≤ pv' f))))
      -- and the transport it produces floats out through the delay
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-∘ᵐ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-ε-substᵀ τ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)

    -- the target: the same two laws, in the same order
    rhs : ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ ·ₑ uₑ) ε ε₂))
            ∘ᵐ μᵀ ∘ᵐ Tᶠ (alg {ε} ∘ᵐ ⟨ pv' , f ⟩ᵐ)
            ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
        ≈ᵐ ε-substᵀ _ ∘ᵐ NF
    rhs =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ (alg ∘ᵐ ⟨ pv' , f ⟩ᵐ)))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-algebraicity τ))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))

-- The state's barrier across a step: the parameter `step-pv` carries forward is
-- the one read off the new state, reindexed along the step's `suc-comp-ren`.
-- Only `DELAY` and `BOX` do anything — the lock the delay adds folds into the
-- barrier, and the cell the box allocates is projected away.

⟨⟩-≤-id : ∀ {X ρ} → (p : ρ ≾ᵣ ρ) → ⟨⟩-≤ {X} p ≈ᵐ idᵐ
⟨⟩-≤-id p = ⟨⟩-≤-irr p ≾ᵣ-refl ∙ ⟨⟩-≤-refl

-- A lock in front of the barrier, refolded: `⊤ᵣ` absorbs it.
delay-suc : ∀ {X ρ} → (q : ρ ·ᵣ ⊤ᵣ ≾ᵣ ⊤ᵣ)
          → (⟨⟩-≤ q ∘ᵐ μ {X} {⊤ᵣ} {ρ}) ∘ᵐ ⟨⊤⟩-η ≈ᵐ ⟨⟩-≤ (≾-⊤ᵣ ρ)
delay-suc {X} {ρ} q =
    ∘ᵐ-congˡ (barrier-μ q)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⊤⟩-η-nat (⟨⟩-≤ (≾-⊤ᵣ ρ)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (Eternalᵒ.α-unit (⟨⊤⟩-eternalᵒ X))
  ∙ ∘ᵐ-identityˡ _

id-suc-step : ∀ {X Y} → (p : ⊤ᵣ ≾ᵣ ⊤ᵣ) → (h : X →ᵐ ⟨ ⊤ᵣ ⟩ᵒ Y)
            → h ≈ᵐ ⟨⟩-≤ p ∘ᵐ h
id-suc-step p h = ≈ᵐ-sym (∘ᵐ-congˡ (⟨⟩-≤-id p) ∙ ∘ᵐ-identityˡ _)

-- A state successor, read as a map into the earlier state's barrier: each lock
-- it passed is extracted, each cell it allocated is projected away.

suc-g : ∀ {Γ Γ'} → {St : 𝕊 Γ} → {St' : 𝕊 Γ'}
      → (q : St ≤ₛ St') → ⟦ toCtx St' ⟧ᶜᵗˣ →ᵐ ⟦ toCtx St ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
suc-g id-suc = ⟨⊤⟩-η
suc-g {St = St} (⟨⟩-suc ρ q) =
  Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ ⟦ toCtx St ⟧ᶜᵗˣ) {ρ} ∘ᵐ ⟨ ρ ⟩ᶠ (suc-g q)
suc-g (∷-suc V q) = suc-g q ∘ᵐ fstᵐ

-- `suc-comp-ren` is the free algebra's extension of `suc-g`: extraction at the
-- outer lock applied to it. The barrier is a free algebra, so the renaming is an
-- algebra morphism, which is what the fold's parameter-naturality needs.

suc-comp-free-at : ∀ {Γ Γ' a} → {St : 𝕊 Γ} → {St' : 𝕊 Γ'}
                 → (q : St ≤ₛ St') → (pf : ≤ₛ-grade q ·ᵣ a ≾ᵣ ⊤ᵣ)
                 → ⟦ suc-comp-ren {ρ'' = ⊤ᵣ} {ρ''' = a} q pf ⟧ʳ
                 ≈ᵐ Eternalᵒ.extᵉ (⟨⊤⟩-eternalᵒ ⟦ toCtx St ⟧ᶜᵗˣ) {a} ∘ᵐ ⟨ a ⟩ᶠ (suc-g q)
suc-comp-free-at {a = a} {St = St} id-suc pf =
    ⟨⟩-≤-irr _ (≾-⊤ᵣ a)
  ∙ ≈ᵐ-sym (barrier-lock {⟦ toCtx St ⟧ᶜᵗˣ} {a})
suc-comp-free-at (⟨⟩-suc ρ q) pf =
    ∘ᵐ-congˡ (suc-comp-free-at q _)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩-μ-nat (suc-g q))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (Eternalᵒ.extᵉ-μ (⟨⊤⟩-eternalᵒ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))
suc-comp-free-at (∷-suc V q) pf =
    ∘ᵐ-congˡ (suc-comp-free-at q pf)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩-∘ᵐ _ _))

suc-comp-free : ∀ {Γ Γ'} → {St : 𝕊 Γ} → {St' : 𝕊 Γ'}
              → (q : St ≤ₛ St') → (pf : ≤ₛ-grade q ·ᵣ ⊤ᵣ ≾ᵣ ⊤ᵣ)
              → ⟦ suc-comp-ren {ρ'' = ⊤ᵣ} {ρ''' = ⊤ᵣ} q pf ⟧ʳ
              ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ (suc-g q)
suc-comp-free q pf =
    suc-comp-free-at q pf
  ∙ ∘ᵐ-congˡ (∘ᵐ-congʳ (⟨⟩-≤-id _) ∙ ∘ᵐ-identityʳ _)

step-pv-state : ∀ {ε₁ ε₃ A A₀} {S S' : 𝕊 []}
              → {M : toCtx S ⊢C⦂ A ‼ ε₁} → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε₃}
              → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
              → (pS : Paramˢ S) → (pM : Paramᶜ M)
              → step-pv (bcᴱ (toCtx S)) r (⟨⊤⟩-η ∘ᵐ ⟦ S ⟧ˢ pS)
              ≈ᵐ ⟦ suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _) ⟧ʳ
                 ∘ᵐ (⟨⊤⟩-η ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM))
step-pv-state APP        pS pM = id-suc-step _ _
step-pv-state MATCH      pS pM = id-suc-step _ _
step-pv-state IF-TRUE    pS pM = id-suc-step _ _
step-pv-state IF-FALSE   pS pM = id-suc-step _ _
step-pv-state SEQ-RET    pS pM = id-suc-step _ _
step-pv-state SEQ-OP     pS pM = id-suc-step _ _
step-pv-state HANDLE-RET pS pM = id-suc-step _ _
step-pv-state HANDLE-OP  pS pM = id-suc-step _ _
step-pv-state UNBOX      pS pM = id-suc-step _ _
step-pv-state SUB-APP    pS pM = id-suc-step _ _
step-pv-state SUB-IF     pS pM = id-suc-step _ _
step-pv-state SUB        pS pM = id-suc-step _ _
step-pv-state (SEQ-STEP r c)    pS (pM , _) = step-pv-state r pS pM
step-pv-state (HANDLE-STEP r c) pS (pM , _) = step-pv-state r pS pM
step-pv-state (BOX {V = V}) pS (pV , _) =
  ≈ᵐ-sym
    (  ∘ᵐ-congˡ (∘ᵐ-congˡ (⟨⟩-≤-id _) ∙ ∘ᵐ-identityˡ _)
     ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
     ∙ ∘ᵐ-congˡ (⟨⊤⟩-η-nat fstᵐ)
     ∙ ∘ᵐ-assoc _ _ _
     ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _) ∙ ∘ᵐ-identityˡ _))
step-pv-state {S = S} (DELAY {τ = τ}) pS pM =
    ∘ᵐ-congʳ (⟨⟩-∘ᵐ _ _)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (barrier-lock {⟦ toCtx S ⟧ᶜᵗˣ} {of-natʳ τ})
  ∙ ≈ᵐ-sym (≈ᵐ-sym (∘ᵐ-assoc _ _ _) ∙ ∘ᵐ-congˡ (delay-suc _))

-- `HANDLE-STEP`: the same assembly as `SEQ-STEP`, with the handler's fold in
-- place of the monad multiplication. `seq-step-core` and `seq-target` are
-- generic in the parameterised algebra, `step-box` is algebra-free, and
-- `T-≤-μᵀ` is matched by `T-alg-of-handlerᵀ-≤`. The clause families at the
-- two states differ by the step's `suc-comp-ren`, so the fold's parameter is
-- reindexed along it (`T-alg-of-handlerᵀ-natᴾ`).

sound-HANDLE-STEP : ∀ {ε₁ ε₂ ε₃ A A₀ B} {S S' : 𝕊 []}
  → {M : toCtx S ⊢C⦂ A ‼ ε₁}
  → (H : (op : Op) → (ε'' : E)
       → toCtx S ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → {M' : toCtx S' ⊢C⦂ A₀ ‼ ε₃}
  → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
  → (pS : Paramˢ S) → (pM : Paramᶜ M) → (pN : Paramᶜ N) → (pM' : Paramᶜ M')
  → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
  → (uH : EffUniformʰ {toCtx S} H pH)
  → ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ S ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ Tᶠ ⟦ step-refines-type r ⟧<:ᵛ
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A₀ ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ pM' ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM)) (stepᵀ r)
  → ⟦ handle M `with H `in N ⟧ᶜᵗ (pM , pN , pH , uH) ∘ᵐ ⟦ S ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ (HANDLE-STEP {H = H} {N = N} r c))
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ} {step-grade r} {ε₃ ·ₑ ε₂}
              (⟦ handle M'
                   `with (λ op ε'' →
                            C-rename
                              (cong-∷-ren (cong-∷-ren
                                (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))))
                              (H op ε''))
                   `in (subCtx (step-refines-type r)
                          (C-rename (cong-∷-ren
                            (suc-comp-ren (step-extends-state r) c)) N)) ⟧ᶜᵗ
                      (pM'
                      , subCtxᴾ (step-refines-type r)
                          (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N)
                          (renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN)
                      , (λ op ε'' →
                           renᶜ (cong-∷-ren (cong-∷-ren
                                  (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _))))
                                (H op ε'') (pH op ε''))
                      , ren-clauses-uniform
                          (suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _)) H pH uH)
                 ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM))
              (stepᵀ r)
sound-HANDLE-STEP {ε₁} {ε₂} {ε₃} {A} {A₀} {B} {S} {S'} {M} H N {M'} r c pS pM pN pM' pH uH ih =
    seq-step-core alg alg-≤ ⟨⊤⟩-η N r c pS pM pN mt ih'
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
      ,   ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
              (⟨ box-merge _ _ (seq-g r) _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
              (step-box r c (seq-g r) pS pM))))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
            (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))
        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ ∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat _))
        ∙ ∘ᵐ-assoc _ _ _
        -- merge the two functorial actions, so the bind is a single `Tᶠ f`
        ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))) ⟩ᵐ-cong))
  -- THE KEY STEP: the handler commutes with the step transition, because a
  -- reduction step never performs an operation
  ∙ ∘ᵐ-congʳ (alg-stepᵀ {B = B} (bcᴱ (toCtx S)) alg alg-≤ alg-delay r
                        (⟨⊤⟩-η ∘ᵐ ⟦ S ⟧ˢ pS) _)
  -- drop the identity the strength's pairing picked up
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
      , ∘ᵐ-congʳ (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-identityʳ _ ⟩ᵐ-cong) ⟩ᵐ-cong))))))
  -- what is under it is the target's denotation, once the parameter carried
  -- across the step is recognised as the new state's
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (
        ∘ᵐ-congʳ (⟨ param-step , ≈ᵐ-refl ⟩ᵐ-cong)
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _
                          ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym alg-natᴾ)
      ∙ ≈ᵐ-sym (seq-target {ε₁} {ε₂} {ε₃} {A} {B} {⟦ toCtx S' ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ}
                  {toCtx S} {toCtx S'} {⟦ hist S' ⟧ᶜᵗˣ}
                  alg' ⟨⊤⟩-η N
                  (suc-comp-ren (step-extends-state r) c)
                  (Tᶠ ⟦ step-refines-type r ⟧<:ᵛ ∘ᵐ ⟦ M' ⟧ᶜᵗ pM')
                  (⟦ S' ⟧ˢ (stepᴾˢ r pS pM)) pN)
      ∙ ≈ᵐ-sym (∘ᵐ-congˡ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
          , subCtx-str {t = step-refines-type r}
              (C-rename (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N)
              (renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN)
              η⊣ (⟦ M' ⟧ᶜᵗ pM') ⟩ᵐ-cong))))))))
  -- … and `seq-coe` fixes the grade
  ∙ seq-coe (step-≾ r) (step-≾ (HANDLE-STEP {H = H} {N = N} r c)) _
  where
    mt : ⟦ hist S' ⟧ᶜᵗˣ →ᵐ Tᵒ ⟦ A ⟧ᵛ ε₃
    mt = (Tᶠ ⟦ step-refines-type r ⟧<:ᵛ ∘ᵐ ⟦ M' ⟧ᶜᵗ pM')
           ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM)

    ih' : ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ S ⟧ˢ pS
        ≈ᵐ T-≤ (step-≾ r)
           ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
                  mt (stepᵀ r)
    ih' = ih
        ∙ ∘ᵐ-congʳ (≈ᵐ-sym (Tᶠ-bind ⟦ step-refines-type r ⟧<:ᵛ
                            (⟦ M' ⟧ᶜᵗ pM' ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM)) (stepᵀ r)))
        ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))

    -- the clause families at the two states differ by the step's own renaming
    fren : Ren [] (toCtx S' ⟨ ⊤ᵣ ⟩) (toCtx S ⟨ ⊤ᵣ ⟩)
    fren = suc-comp-ren (step-extends-state r) (≾-⊤ᵣ _)

    H' : (op : Op) → (ε'' : E)
       → toCtx S' ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
    H' op ε'' = C-rename (cong-∷-ren (cong-∷-ren fren)) (H op ε'')

    pH' : ∀ op ε'' → Paramᶜ (H' op ε'')
    pH' op ε'' = renᶜ (cong-∷-ren (cong-∷-ren fren)) (H op ε'') (pH op ε'')

    uH' = ren-clauses-uniform fren H pH uH

    f : ⟦ toCtx S' ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ →ᵐ ⟦ toCtx S ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ
    f = ⟦ fren ⟧ʳ

    -- `f` is the free-algebra morphism induced by `suc-g`
    f≈ : f ≈ᵐ ⟨⊤⟩-μ ∘ᵐ ⟨ ⊤ᵣ ⟩ᶠ (suc-g (step-extends-state r))
    f≈ = suc-comp-free (step-extends-state r) (≾-⊤ᵣ _)

    alg : ∀ {ε} → ⟦ toCtx S ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε
        →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂)
    alg = T-alg-of-handlerᵀ (bcᴱ (toCtx S)) (⟦_⟧ʰᵗ {toCtx S} H pH uH)

    alg' : ∀ {ε} → ⟦ toCtx S' ⟨ ⊤ᵣ ⟩ ⟧ᶜᵗˣ ×ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε
         →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂)
    alg' = T-alg-of-handlerᵀ (bcᴱ (toCtx S')) (⟦_⟧ʰᵗ {toCtx S'} H' pH' uH')

    alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
          → alg {εb} ∘ᵐ mapˣᵐ idᵐ (T-≤ q) ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa}
    alg-≤ q = T-alg-of-handlerᵀ-≤ (bcᴱ (toCtx S)) (⟦_⟧ʰᵗ {toCtx S} H pH uH) q

    alg-delay : ∀ {ε'} → (τ : ℕ)
              → alg {of-natᵉ τ ·ₑ ε'}
                  ∘ᵐ mapˣᵐ idᵐ (delayᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {ε'} τ)
              ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
                  ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (alg {ε'})
                  ∘ᵐ []-monoidal
                  ∘ᵐ mapˣᵐ (Eternalᵒ.necᵉ (bcᴱ (toCtx S)) {of-natʳ τ}) idᵐ
    alg-delay τ =
      T-alg-of-handlerᵀ-delayᵀ τ (bcᴱ (toCtx S)) (⟦_⟧ʰᵗ {toCtx S} H pH uH)

    ⟦H'⟧ʰᵗ-nat : ∀ op ε''
               → clauseᵀ (⟦_⟧ʰᵗ {toCtx S'} H' pH' uH') op ε''
               ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {toCtx S} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
    ⟦H'⟧ʰᵗ-nat op ε'' =
        ∘ᵐ-congˡ (C-rename-nat (cong-∷-ren (cong-∷-ren fren))
                    (H op ε'') (pH op ε''))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (adapt-commute _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

    f-necᵉ : ∀ {ρ₁} → [ ρ₁ ]ᶠ f ∘ᵐ Eternalᵒ.necᵉ (bcᴱ (toCtx S'))
                    ≈ᵐ Eternalᵒ.necᵉ (bcᴱ (toCtx S)) ∘ᵐ f
    f-necᵉ =
        ∘ᵐ-congˡ ([]-congᶠ f≈)
      ∙ free-necᵉ-nat _ (free-extᵉ-nat (suc-g (step-extends-state r)))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym f≈)

    alg-natᴾ : ∀ {ε} → alg' {ε} ≈ᵐ alg {ε} ∘ᵐ mapˣᵐ f idᵐ
    alg-natᴾ =
      T-alg-of-handlerᵀ-natᴾ (bcᴱ (toCtx S)) (bcᴱ (toCtx S'))
        f f-necᵉ (⟦_⟧ʰᵗ {toCtx S} H pH uH) _ ⟦H'⟧ʰᵗ-nat

    param-step : step-pv (bcᴱ (toCtx S)) r (⟨⊤⟩-η ∘ᵐ ⟦ S ⟧ˢ pS)
               ≈ᵐ f ∘ᵐ (⟨⊤⟩-η ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM))
    param-step = step-pv-state r pS pM

-- `SEQ-OP`: sequencing a computation that begins with an operation is the
-- operation with the sequencing pushed into its continuation
-- (`opᵀ-algebraicity`, `strᵀ-opᵀ-algebraicity`). The environment is pushed
-- under the continuation's box by `exp-strᵐ`.

-- Reassociating the operation's arguments: `strᵀ-opᵀ-algebraicity` hands the
-- operation back its parameter and pairs the environment with the (boxed)
-- continuation, putting the parameter back in front of an actual `perform`'s
-- `⟨ env , ⟨ param , cont ⟩ᵐ ⟩ᵐ` argument.

op-pair : ∀ {X E P Q R} → (v : X →ᵐ P) → (e : X →ᵐ E) → (c : X →ᵐ Q)
        → (F : E ×ᵐ Q →ᵐ R)
        → mapˣᵐ idᵐ F ∘ᵐ ⟨ fstᵐ ∘ᵐ sndᵐ , ⟨ fstᵐ , sndᵐ ∘ᵐ sndᵐ ⟩ᵐ ⟩ᵐ
            ∘ᵐ ⟨ e , ⟨ v , c ⟩ᵐ ⟩ᵐ
        ≈ᵐ ⟨ v , F ∘ᵐ ⟨ e , c ⟩ᵐ ⟩ᵐ
op-pair v e c F =
    ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ
      (⟨ ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-fstᵐ _ _
       , ⟨⟩ᵐ-∘ _ _ _
         ∙ ⟨ ⟨⟩ᵐ-fstᵐ _ _
           , ∘ᵐ-assoc _ _ _ ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _) ∙ ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong ⟩ᵐ-cong)
  ∙ mapˣᵐ-∘⟨⟩ _ _ _ _
  ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong

-- The environment the operation's continuation receives: weakening past the
-- bound arity value outside the second transposition (`_ ∘ᵐ fstᵐ`) or inside
-- it (the syntax's `cong-⟨⟩-ren wk-ren`) agree, by naturality of `η⊣`.

op-env : ∀ {X Y d ε} → (a : mapᵉ d ·ᵣ mapᵉ ε ≾ᵣ mapᵉ (d ·ₑ ε))
       → ([ mapᵉ ε ]ᶠ (⟨⟩-≤ a ∘ᵐ μ) ∘ᵐ η⊣ {⟨ mapᵉ d ⟩ᵒ X} {mapᵉ ε}) ∘ᵐ fstᵐ {_} {Y}
       ≈ᵐ [ mapᵉ ε ]ᶠ (⟨⟩-≤ a ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ)
            ∘ᵐ η⊣ {⟨ mapᵉ d ⟩ᵒ X ×ᵐ Y} {mapᵉ ε}
op-env a =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat fstᵐ))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  ∙ ∘ᵐ-congˡ ([]-congᶠ (∘ᵐ-assoc _ _ _))

-- The heart of `SEQ-OP`: splitting the environment's box into the
-- operation's and the continuation's grades (`box-split`) matches the
-- syntax's refolding of the two locks into one (`⟨⟩-μ-ren`).

seq-op-box : ∀ {X A B ε ε'} → (op : Op)
  → (alg : Tᵒ (Tᵒ B ε') ε →ᵐ Tᵒ B (ε ·ₑ ε'))
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ alg)
      ∘ᵐ [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ n))
      ∘ᵐ ( [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (strᵀ {_} {A} {ε}) ∘ᵐ exp-strᵐ)
         ∘ᵐ []-monoidal
         ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ )
      ∘ᵐ ⟨ η⊣ {X} {mapᵉ (op-grade op ·ₑ ε)}
         , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ m) ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)} ⟩ᵐ
  ≈ᵐ [ mapᵉ (op-grade op) ]ᶠ
       (curryᵐ (alg ∘ᵐ Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ))
     ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)}
seq-op-box {X} {A} {B} {ε} {ε'} op alg m n rn ern =
  -- bring the strength law's reshuffle up against the operation's arguments
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  -- split the environment's box: once at the operation's grade, once at the
  -- continuation's, the two pasts refolded by `μ`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (  mapˣᵐ-∘⟨⟩ _ _ _ _
       ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ box-split _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))))
  -- and pair the two transposed halves under one box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _)))
  -- collect everything under a single box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  -- inside the box: the environment is pushed under the exponential, and the
  -- three postcompositions collapse into the sequenced body
  ∙ ∘ᵐ-congˡ ([]-congᶠ
      (  ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (exp-strᵐ-⟨⟩ _ _)))
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _))
       ∙ ∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _)
       ∙ map⇒ᵐ-curryᵐ _ _))
  -- and that body is the target's, once the syntax's renaming is recognised as
  -- the environment the continuation actually receives
  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (≈ᵐ-sym
      (  ∘ᵐ-congʳ (∘ᵐ-congˡ (T-∘ᵐ n (mapˣᵐ rn idᵐ)))
       ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ body))))
  where
    -- the renaming the syntax applies to the continuation *is* the environment
    -- the strength hands it: a map on the strength's boxed component (`strᵀ-natˡ`),
    -- and that map is `op-env`
    body : alg ∘ᵐ Tᶠ n ∘ᵐ Tᶠ (mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
         ≈ᵐ alg ∘ᵐ Tᶠ n ∘ᵐ strᵀ
              ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣)
                     ∘ᵐ fstᵐ
                 , m ⟩ᵐ
    body =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ rn)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-congˡ ([]-congᶠ ern) ∙ ≈ᵐ-sym (op-env _) , ≈ᵐ-refl ⟩ᵐ-cong)))

-- The commuting conversion, at the level of the model: `strᵀ-opᵀ-algebraicity`
-- puts the environment inside the operation's continuation, `opᵀ-nat` puts
-- the sequel `n` there too, and `opᵀ-algebraicity` puts the multiplication
-- there, leaving the `ε-substᵀ` that reassociates the grades.

seq-op-core : ∀ {X Y A B ε ε'} → (op : Op)
            -- the algebra that collapses the two monad layers …
            → (alg : ∀ {ε₀} → Tᵒ (Tᵒ B ε') ε₀ →ᵐ Tᵒ B (ε₀ ·ₑ ε'))
            -- … and what it does to an operation: re-emit it
            -- (`opᵀ-algebraicity`), pushed into the operation's continuation.
            → (cl : (⟦ param op ⟧ᵍ
                       ×ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ B (ε ·ₑ ε')))
                    →ᵐ Tᵒ B (op-grade op ·ₑ (ε ·ₑ ε')))
            → (alg-op : alg {op-grade op ·ₑ ε} ∘ᵐ opᵀ {ε = ε} op
                      ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
                         ∘ᵐ cl
                         ∘ᵐ mapˣᵐ idᵐ
                              ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (alg {ε}))))
            → (ea : Y ≡ ⟦ arity op ⟧ᵍ)
            → (v : X →ᵐ ⟦ param op ⟧ᵍ)
            → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y) →ᵐ Tᵒ A ε)
            → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
            → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y)
                    →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
            → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
            → alg ∘ᵐ Tᶠ n ∘ᵐ strᵀ
                ∘ᵐ ⟨ η⊣
                   , opᵀ op
                       ∘ᵐ ⟨ v
                          , [ mapᵉ (op-grade op) ]ᶠ
                              (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                                    →ᵐ Tᵒ A ε)
                                             ea m))
                              ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
            ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
               ∘ᵐ cl
               ∘ᵐ ⟨ v
                  , [ mapᵉ (op-grade op) ]ᶠ
                      (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                            →ᵐ Tᵒ B (ε ·ₑ ε'))
                                     ea
                                     (alg ∘ᵐ Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ
                                        ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)))
                    ∘ᵐ η⊣ ⟩ᵐ
seq-op-core op alg cl alg-op refl v m n rn ern =
  -- the operation is a map on the strength's monadic component …
    ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))))
  -- … so the strength pushes into it, carrying the environment under its box
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- the reshuffle just hands the parameter back and pairs environment with
  -- continuation
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ op-pair _ _ _ _)))
  -- the sequel is natural, so it too goes into the continuation
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op n)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- and the operation is algebraic for the algebra, so that goes in too —
  -- leaving the grade reassociation behind
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ alg-op
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- collect the three maps on the continuation
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
      (  ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
       ∙ mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong))
  -- what they amount to is the sequenced continuation
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl , seq-op-box op alg m n rn ern ⟩ᵐ-cong))

-- The algebra-free counterparts of `seq-op-box`/`seq-op-core`: `str-op-box` and
-- `str-op` push a sequel under an operation without collapsing the two monad
-- layers with an algebra (the codomain stays `Tᵒ (Tᵒ B ε') ε`). What remains is
-- the strength's own algebraicity. Used by the `handle-perform` soundness, where
-- the handler carries a live eternal parameter and is not a plain algebra.

str-op-box : ∀ {X A B ε ε'} → (op : Op)
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ ⟦ arity op ⟧ᵍ)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Tᶠ n))
      ∘ᵐ ( [ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (strᵀ {_} {A} {ε}) ∘ᵐ exp-strᵐ)
         ∘ᵐ []-monoidal
         ∘ᵐ mapˣᵐ (δ ∘ᵐ []-≤ (≾ᵣ-reflexive (sym map-·ᵉ))) idᵐ )
      ∘ᵐ ⟨ η⊣ {X} {mapᵉ (op-grade op ·ₑ ε)}
         , [ mapᵉ (op-grade op) ]ᶠ (curryᵐ m) ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)} ⟩ᵐ
  ≈ᵐ [ mapᵉ (op-grade op) ]ᶠ
       (curryᵐ (Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ))
     ∘ᵐ η⊣ {X} {mapᵉ (op-grade op)}
str-op-box {X} {A} {B} {ε} {ε'} op m n rn ern =
  -- bring the strength law's reshuffle up against the operation's arguments
    ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- split the environment's box, and pair the two transposed halves under one
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (  mapˣᵐ-∘⟨⟩ _ _ _ _
       ∙ ⟨ ∘ᵐ-assoc _ _ _ ∙ box-split _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (η⊣-⟨⟩ _ _))
  -- collect everything under a single box
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
  -- inside the box: push the environment under the exponential and collapse
  ∙ ∘ᵐ-congˡ ([]-congᶠ
      (  ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (exp-strᵐ-⟨⟩ _ _))
       ∙ ∘ᵐ-congʳ (map⇒ᵐ-curryᵐ _ _)
       ∙ map⇒ᵐ-curryᵐ _ _))
  -- and recognise the syntax's renaming as the environment `n` receives
  ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (≈ᵐ-sym
      (  ∘ᵐ-congˡ (T-∘ᵐ n (mapˣᵐ rn idᵐ))
       ∙ ∘ᵐ-assoc _ _ _
       ∙ body))))
  where
    body : Tᶠ n ∘ᵐ Tᶠ (mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ
         ≈ᵐ Tᶠ n ∘ᵐ strᵀ
              ∘ᵐ ⟨ ([ mapᵉ ε ]ᶠ (⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ) ∘ᵐ η⊣)
                     ∘ᵐ fstᵐ
                 , m ⟩ᵐ
    body =
        ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-natˡ rn))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ≈ᵐ-refl , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ
          (⟨ ∘ᵐ-congˡ ([]-congᶠ ern) ∙ ≈ᵐ-sym (op-env _) , ≈ᵐ-refl ⟩ᵐ-cong))

str-op : ∀ {X Y A B ε ε'} → (op : Op)
  → (ea : Y ≡ ⟦ arity op ⟧ᵍ)
  → (v : X →ᵐ ⟦ param op ⟧ᵍ)
  → (m : (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y) →ᵐ Tᵒ A ε)
  → (n : (⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X ×ᵐ A) →ᵐ Tᵒ B ε')
  → (rn : ⟨ mapᵉ ε ⟩ᵒ (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ Y)
          →ᵐ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ᵒ X)
  → rn ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
  → Tᶠ n ∘ᵐ strᵀ
      ∘ᵐ ⟨ η⊣
         , opᵀ op
             ∘ᵐ ⟨ v
                , [ mapᵉ (op-grade op) ]ᶠ
                    (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                          →ᵐ Tᵒ A ε)
                                   ea m))
                    ∘ᵐ η⊣ ⟩ᵐ ⟩ᵐ
  ≈ᵐ opᵀ op
     ∘ᵐ ⟨ v
        , [ mapᵉ (op-grade op) ]ᶠ
            (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ X ×ᵐ O)
                                  →ᵐ Tᵒ (Tᵒ B ε') ε)
                           ea
                           (Tᶠ (n ∘ᵐ mapˣᵐ rn idᵐ) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , m ⟩ᵐ)))
          ∘ᵐ η⊣ ⟩ᵐ
str-op op refl v m n rn ern =
  -- the operation is a map on the strength's monadic component …
    ∘ᵐ-congʳ (∘ᵐ-congʳ
        (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))
  -- … so the strength pushes into it, carrying the environment under its box
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (strᵀ-opᵀ-algebraicity op))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  -- the reshuffle hands the parameter back and pairs environment with cont.
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _ ∙ op-pair _ _ _ _))
  -- the sequel is natural, so it too goes into the continuation
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (opᵀ-nat op n))
  ∙ ∘ᵐ-assoc _ _ _
  -- collect the map on the continuation, then apply `str-op-box`
  ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , str-op-box op m n rn ern ⟩ᵐ-cong)

-- Cancelling the ground-type coercions.
--
-- `⟦_⟧ᶜᵗ` coerces an operation's parameter and arity between their value-type
-- and ground-type interpretations, and `⟦_⟧ʰᵗ` coerces them straight back. The
-- two cancel — which is why the handler's clause may be applied to the very
-- arguments the operation carries.

gty-cancelᵛ : ∀ {X Y Y'} → (e : Y ≡ Y') → (f : X →ᵐ Y)
            → subst (λ O → Y' →ᵐ O) (sym e) idᵐ ∘ᵐ subst (λ O → X →ᵐ O) e f
            ≈ᵐ f
gty-cancelᵛ refl f = ∘ᵐ-identityˡ f

-- The arity coercion cancels inside the operation's boxed continuation
-- (`map⇒ᵐ-idᵐ`).
arity-box : ∀ {Z W W' P Yv Yg} → (e : Yv ≡ Yg)
          → (alg : P ×ᵐ W' →ᵐ W) → (p : Z →ᵐ P) → (c : Z ×ᵐ Yv →ᵐ W')
          → map⇒ᵐ (subst (λ O → O →ᵐ Yg) (sym e) idᵐ) idᵐ
              ∘ᵐ curryᵐ (alg ∘ᵐ ⟨ p ∘ᵐ fstᵐ
                                , subst (λ O → Z ×ᵐ O →ᵐ W') e c ⟩ᵐ)
          ≈ᵐ curryᵐ (alg ∘ᵐ ⟨ p ∘ᵐ fstᵐ , c ⟩ᵐ)
arity-box refl alg p c = ∘ᵐ-congˡ map⇒ᵐ-idᵐ ∙ ∘ᵐ-identityˡ _

-- Applying the fold's boxed continuation to the actual (curried) continuation:
-- the `appᵐ` of the law's body meets the `curryᵐ` the operation carries, and the
-- exponential β-rule collapses them.
cont-collapse : ∀ {P X Y Z W} → (alg : P ×ᵐ Z →ᵐ W) → (p : X →ᵐ P)
              → (c : X ×ᵐ Y →ᵐ Z)
              → curryᵐ (alg ∘ᵐ ⟨ fstᵐ ∘ᵐ fstᵐ
                               , appᵐ ∘ᵐ ⟨ sndᵐ ∘ᵐ fstᵐ , sndᵐ ⟩ᵐ ⟩ᵐ)
                  ∘ᵐ ⟨ p , curryᵐ c ⟩ᵐ
              ≈ᵐ curryᵐ (alg ∘ᵐ ⟨ p ∘ᵐ fstᵐ , c ⟩ᵐ)
cont-collapse alg p c =
    ≈ᵐ-sym (curryᵐ-nat ⟨ p , curryᵐ c ⟩ᵐ _)
  ∙ curryᵐ-cong
      (  ∘ᵐ-assoc _ _ _
       ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                   ∙ ⟨   ∘ᵐ-assoc _ _ _
                       ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                       ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-fstᵐ _ _)
                     ,   ∘ᵐ-assoc _ _ _
                       ∙ ∘ᵐ-congʳ (  ⟨⟩ᵐ-∘ _ _ _
                                   ∙ ⟨   ∘ᵐ-assoc _ _ _
                                       ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-fstᵐ _ _)
                                       ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
                                       ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
                                     , ⟨⟩ᵐ-sndᵐ _ _ ⟩ᵐ-cong)
                       ∙ ≈ᵐ-sym (uncurryᵐ-nat (curryᵐ c) idᵐ)
                       ∙ uncurryᵐ-cong (∘ᵐ-identityˡ _)
                       ∙ curryᵐ-uncurryᵐ-iso c ⟩ᵐ-cong))

-- SEQ-OP: sequencing an operation is the operation with the sequencing pushed
-- into its continuation. The state plays no part — the rule is a plain equation
-- in an arbitrary context.

sound-SEQ-OP : ∀ {Γ A B ε ε'} → (op : Op)
             → (V : Γ ⊢V⦂ type-of-gtype (param op))
             → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
             → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε')
             → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
             → ⟦ perform op V M ⨟ N ⟧ᶜᵗ ((pV , pM) , pN)
             ≈ᵐ ⟦ ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
                    (perform op V
                      (M ⨟ C-rename
                             (cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
                                          ∘ʳ cong-⟨⟩-ren wk-ren))
                             N)) ⟧ᶜᵗ
                  (ε-substᴾ (sym (·ₑ-assoc (op-grade op) ε ε'))
                     (perform op V (M ⨟ C-rename (cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N))
                     (pV , pM , renᶜ (cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N pN))
sound-SEQ-OP {Γ} {A} {B} {ε} {ε'} op V M N pV pM pN =
    seq-op-core op μᵀ (opᵀ op) (opᵀ-algebraicity op) (ty-gty (arity op))
      (subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV))
      (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) ⟦ ren ⟧ʳ ern
  ∙ ≈ᵐ-sym
      (  sound-ε-subst (sym (·ₑ-assoc (op-grade op) ε ε'))
           (perform op V (M ⨟ C-rename (cong-∷-ren ren) N))
           (pV , pM , renᶜ (cong-∷-ren ren) N pN)
       ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (⟨ ≈ᵐ-refl
           , ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (substᵈ-≈ (ty-gty (arity op))
               (∘ᵐ-congʳ (∘ᵐ-congˡ
                 (T-congᶠ (C-rename-nat (cong-∷-ren ren) N pN))))))) ⟩ᵐ-cong)))
  where
    ren : Ren [] ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
                 (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
    ren = (eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    -- the renaming is the `μ`-refold of the two locks, after weakening past the
    -- arity value the continuation binds
    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

-- `HANDLE-OP`: handling an operation applies the matching clause, with the
-- rest of the handled computation boxed up as the clause's continuation, the
-- box being what stops the continuation running before `op-grade op` worth
-- of time has passed. The equation is `SEQ-OP`'s with the handler's fold
-- (`T-alg-of-handlerᵀ-opᵀ`) in place of the monad multiplication
-- (`opᵀ-algebraicity`); the eternal parameter is carried under the
-- operation's box by `necᵉ`.

sound-HANDLE-OP : ∀ {Γ A B ε ε''} → (op : Op)
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                       ⊢C⦂ A ‼ ε)
                → (H : (op' : Op) → (ε' : E)
                     → Γ ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op')
                          ∷ [ mapᵉ (op-grade op') ]
                              (type-of-gtype (arity op') ⇒ B ‼ ε')
                       ⊢C⦂ B ‼ (op-grade op' ·ₑ ε'))
                → (N : Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩ ∷ A ⊢C⦂ B ‼ ε'')
                → (pV : Paramᵛ V) → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → (pH : ∀ op' ε' → Paramᶜ (H op' ε'))
                → (uH : EffUniformʰ {Γ} H pH)
                → ⟦ handle perform op V M `with H `in N ⟧ᶜᵗ
                     ((pV , pM) , pN , pH , uH)
                ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε''))
                   ∘ᵐ ⟦ box (lam (handle M
                                   `with (λ op' ε' →
                                            C-rename (cong-∷-ren (cong-∷-ren
                                              (barrier-wk-ren (mapᵉ (op-grade op))
                                                              (type-of-gtype (arity op)))))
                                              (H op' ε'))
                                   `in (C-rename (cong-∷-ren
                                          ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
                                           ∘ʳ cong-⟨⟩-ren wk-ren)) N)))
                            (C-rename (cong-∷-ren (cong-∷-ren (barrier-ren {Γ})))
                                       (H op (ε ·ₑ ε''))
                             [ split-∷ split-[] ↦ V ]c) ⟧ᶜᵗ
                     ( (pM
                       , renᶜ (cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N pN
                       , (λ op' ε' →
                            renᶜ (cong-∷-ren (cong-∷-ren (barrier-wk-ren (mapᵉ (op-grade op)) (type-of-gtype (arity op))))) (H op' ε') (pH op' ε'))
                       , ren-clauses-uniform
                           (barrier-wk-ren (mapᵉ (op-grade op)) (type-of-gtype (arity op)))
                           H pH uH)
                     , subᶜ (C-rename (cong-∷-ren (cong-∷-ren (barrier-ren {Γ})))
                                     (H op (ε ·ₑ ε'')))
                            (split-∷ split-[]) V
                            (renᶜ (cong-∷-ren (cong-∷-ren (barrier-ren {Γ})))
                                  (H op (ε ·ₑ ε'')) (pH op (ε ·ₑ ε'')))
                            pV )
sound-HANDLE-OP {Γ} {A} {B} {ε} {ε''} op V M H N pV pM pN pH uH =
  -- `str-op` moves the sequel `N` into the operation's boxed continuation
    ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
              , str-op op (ty-gty (arity op)) Vp (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN)
                  ⟦ ren ⟧ʳ ern ⟩ᵐ-cong)
  -- re-form `mapˣᵐ idᵐ (opᵀ op)` and apply the fold's operation law
  ∙ ∘ᵐ-congʳ (  ⟨ ≈ᵐ-sym (∘ᵐ-identityˡ _) , ≈ᵐ-refl ⟩ᵐ-cong
              ∙ ≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-opᵀ op (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH))
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
  -- what is left is the reduct: the clause fired at `Γ`, applied to the
  -- parameter and to the boxed continuation the `box` allocates
  ∙ ∘ᵐ-congʳ tgt
  where
    Vp = subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)

    ren : Ren [] ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
                 (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
    ren = (eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

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
          ∙ ⟨   ∘ᵐ-congˡ (Eternalᵒ.necᵉ-mate (bcᴱ Γ))
              ∙ ∘ᵐ-assoc _ _ _
              ∙ ∘ᵐ-congʳ (≈ᵐ-sym (η⊣-nat (⟨⊤⟩-η {⟦ Γ ⟧ᶜᵗˣ})))
              ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
              ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))
      ∙ ∘ᵐ-congʳ (η⊣-⟨⟩ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
      ∙ ∘ᵐ-congˡ ([]-congᶠ (cont-collapse _ _ _))

    -- the box the reduct allocates is the operation's continuation: the handled
    -- remainder, abstracted over the arity value, its arity coercions cancelled
    -- by `arity-box` and its inner handle reconciled by `handle-op-cont`
    tgt =
        ≈ᵐ-sym (clause-sound op H pH uH V pV _)
      ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
          ,   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            ∙ ∘ᵐ-congˡ ([]-congᶠ (arity-box (ty-gty (arity op)) _ _ _))
            ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                (≈ᵐ-sym (handle-op-cont H M N ren pM pN pH uH))))
          ⟩ᵐ-cong)
