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
open import Syntax.RenActions S using (V-rename; C-rename; unbox⇒var; var-rename)
open import Syntax.Substitutions S

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
       Cat (GradeSystem.RGrade Grades) Fut Pst Adj using (Eternalᵒ)
import DenotationalSemantics.Model.HandlerAlgebra S Cat Fut Pst Adj GTy as HC
open import OperationalSemantics.Soundness.Preservation.HandleOpCont S Cat Fut Pst Adj GTy Mon GE
  using (handle-op-cont; ren-ᴱ-∷≡restrict)
open import OperationalSemantics.Soundness.Preservation.HandleOpClause S Cat Fut Pst Adj GTy Mon GE
  using (term∅; ∅-terminal; clause-sound)

open import OperationalSemantics.Soundness.Preservation.Step S Cat Fut Pst Adj GTy Mon GE public

-- THE HANDLER COMMUTES WITH A STEP TRANSITION
--
-- A reduction step never performs an operation: `stepᵀ r` is `ηᵀ` for every
-- rule but `DELAY`, where it is a tick. So handling the effects a step produces
-- gives the same result whether the handler sits inside the step or outside it,
-- which is what lets `HANDLE-STEP` move the transition out of the handler's
-- argument and into the `⋄` of the target configuration.
--
-- The equation holds only for step transitions: `alg ∘ᵐ μᵀ ≈ᵐ μᵀ ∘ᵐ Tᶠ alg` is
-- false for a general tree, whose outer layer's operations would be handled on
-- one side and merely flattened on the other.

-- The algebra commutes with a grade transport (derivable from `alg-≤`).

alg-ε-subst : ∀ {B ε₂ ε₁' ε₂'}
            → (alg : ∀ {ε} → Tᵒ (Tᵒ B ε₂) ε →ᵐ Tᵒ B (ε ·ₑ ε₂))
            → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                     → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
            → (e : ε₁' ≡ ε₂')
            → alg {ε₂'} ∘ᵐ ε-substᵀ e
            ≈ᵐ ε-substᵀ (cong (_·ₑ ε₂) e) ∘ᵐ alg {ε₁'}
alg-ε-subst alg alg-≤ e =
    ∘ᵐ-congʳ (T-≤-≡ e)
  ∙ alg-≤ (≾ₑ-reflexive e)
  ∙ ∘ᵐ-congˡ (T-≤-irr _ (≾ₑ-reflexive (cong (_·ₑ _) e)))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (T-≤-≡ (cong (_·ₑ _) e)))

-- The `ηᵀ` case: a step that performs nothing. Both sides collapse by the
-- monad's left-unit law, and the algebra passes the returned value through
-- (`T-alg-of-handlerᵀ-ηᵀ`).

alg-ηᵀ : ∀ {B Y ε ε₂}
       → (alg : ∀ {ε'} → Tᵒ (Tᵒ B ε₂) ε' →ᵐ Tᵒ B (ε' ·ₑ ε₂))
       → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
       → (alg-η : alg {uₑ} ∘ᵐ ηᵀ {Tᵒ B ε₂}
                ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂)))
       → (f : Y →ᵐ Tᵒ (Tᵒ B ε₂) ε)
       → alg {uₑ ·ₑ ε} ∘ᵐ μᵀ {Tᵒ B ε₂} {uₑ} {ε} ∘ᵐ Tᶠ f ∘ᵐ ηᵀ
       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc uₑ ε ε₂))
           ∘ᵐ μᵀ {B} {uₑ} {ε ·ₑ ε₂} ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f) ∘ᵐ ηᵀ
alg-ηᵀ {ε = ε} {ε₂ = ε₂} alg alg-≤ alg-η f =
  -- pull `ηᵀ` to the front, then the unit law collapses `μᵀ ∘ ηᵀ`
    ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (ηᵀ-nat f)))
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ T-μ∘η≡id)
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  -- the algebra passes the transport through
  ∙ ∘ᵐ-congˡ (alg-ε-subst alg alg-≤ (sym (·ₑ-identityˡ ε)))
  ∙ ∘ᵐ-assoc _ _ _
  -- and the two accumulated transports agree (`uip`), so the same chain
  -- rebuilds the right-hand side
  ∙ ∘ᵐ-congˡ (≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip))
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym (ε-substᵀ-trans _ _))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym T-μ∘η≡id))
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (ηᵀ-nat (alg ∘ᵐ f)))

-- The step transition commutes with the handler, by induction on the
-- reduction. Ten rules transition by `ηᵀ` (`alg-ηᵀ`); `DELAY` ticks, and the
-- fold *re-delays* (`T-alg-of-handlerᵀ-delayᵀ`), so the tick passes through;
-- the two step rules inherit their transition from the sub-step.

alg-stepᵀ : ∀ {ε ε₂ ε₁' ε₃' A B} {S S' : 𝕊 []}
          → {M : toCtx S ⊢C⦂ A ‼ ε₁'} → {M' : toCtx S' ⊢C⦂ A ‼ ε₃'}
          → (alg : ∀ {ε'} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε' →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε' ·ₑ ε₂))
          → (alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
                   → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa})
          → (alg-η : alg {uₑ} ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂}
                   ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂)))
          → (alg-delay : ∀ {ε'} → (τ : ℕ)
                       → alg {of-natᵉ τ ·ₑ ε'} ∘ᵐ delayᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {ε'} τ
                       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
                           ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (alg {ε'}))
          → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
          → (f : ⟦ hist S' ⟧ᶜᵗˣ →ᵐ Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε)
          → alg {step-grade r ·ₑ ε} ∘ᵐ μᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {step-grade r} {ε}
              ∘ᵐ Tᶠ f ∘ᵐ stepᵀ r
          ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (step-grade r) ε ε₂))
              ∘ᵐ μᵀ {⟦ B ⟧ᵛ} {step-grade r} {ε ·ₑ ε₂}
              ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f) ∘ᵐ stepᵀ r
alg-stepᵀ alg alg-≤ alg-η alg-delay APP        f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay MATCH      f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay SEQ-RET    f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay SEQ-OP     f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay HANDLE-RET f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay HANDLE-OP  f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay BOX        f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay UNBOX      f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ alg alg-≤ alg-η alg-delay COERCE     f = alg-ηᵀ alg alg-≤ alg-η f
alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay (SEQ-STEP r c) f =
  alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay r f
alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay (HANDLE-STEP r c) f =
  alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay r f
alg-stepᵀ {ε = ε} {ε₂ = ε₂} {B = B} alg alg-≤ alg-η alg-delay (DELAY {τ = τ}) f =
  -- Both sides reach the same normal form: the tick, with the *whole* bind
  -- carried under the box. `alg-ηᵀ` does the work there — under `[ of-natʳ τ ]`
  -- the step has become the trivial one.
  lhs ∙ ∘ᵐ-congˡ (≡→≈ᵐ (cong (λ z → ε-substᵀ z) uip)) ∙ ≈ᵐ-sym rhs
  where
    -- the common normal form
    NF : _ →ᵐ _
    NF = delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (μᵀ ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f) ∘ᵐ ηᵀ) ∘ᵐ η⊣

    -- the source: pull the tick out of the bind, collect everything under the
    -- box, then `alg-ηᵀ`
    lhs : alg {of-natᵉ τ ·ₑ uₑ ·ₑ ε} ∘ᵐ μᵀ ∘ᵐ Tᶠ f
            ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
        ≈ᵐ ε-substᵀ _ ∘ᵐ NF
    lhs =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ f))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (delayᵀ-algebraicity τ))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (alg-ε-subst alg alg-≤ (sym (·ₑ-assoc (of-natᵉ τ) uₑ ε)))
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-congˡ (alg-delay τ)))
      -- collect the transports, and the `[ of-natʳ τ ]ᶠ`-images into one
      ∙ ∘ᵐ-congʳ (∘ᵐ-congˡ (∘ᵐ-assoc _ _ _))
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congˡ (ε-substᵀ-trans _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _)))))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))))
      -- under the box the step has become the trivial one: `alg-ηᵀ` applies
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ ([]-congᶠ (alg-ηᵀ alg alg-≤ alg-η f))))
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
            ∘ᵐ μᵀ ∘ᵐ Tᶠ (alg {ε} ∘ᵐ f)
            ∘ᵐ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)
        ≈ᵐ ε-substᵀ _ ∘ᵐ NF
    rhs =
        ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
      ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (delayᵀ-nat τ (alg ∘ᵐ f)))))
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

-- COLLAPSING THE HANDLER'S ETERNAL PARAMETER AT RUNTIME CONTEXTS
--
-- In the operational soundness proofs every `handle` sits at a runtime context
-- `Γ` with `Γ ᴱ ≡ []`, so its eternal-parameter object `⟦ Γ ᴱ ⟧` is terminal.
-- The handler's fold therefore collapses to a plain (parameter-free) algebra
-- `Halg`, letting the `HANDLE-*` proofs reuse the `⨟`/`μᵀ` machinery verbatim.

-- `term∅` (the terminal map into `⟦ Γ ᴱ ⟧` when `Γ ᴱ ≡ []`) and `∅-terminal`
-- (uniqueness of such maps) are imported from `HandleOpClause`.

-- The parameter-free algebra a `handle` at a runtime context folds with.
Halg : ∀ {Γ B ε₂} → (e : Γ ᴱ ≡ [])
     → (H : (op : Op) → (ε'' : E)
          → Γ ᴱ ∷ type-of-gtype (param op)
               ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
            ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
     → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
     → (uH : EffUniformʰ {Γ} H pH)
     → ∀ {ε} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂)
Halg {Γ} e H pH uH = T-alg-of-handlerᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH) ∘ᵐ ⟨ term∅ e , idᵐ ⟩ᵐ

-- `Halg`'s sub-effecting and unit laws, from the fold's own laws plus the
-- terminality of the (trivial) parameter.
Halg-≤ : ∀ {Γ B ε₂} → (e : Γ ᴱ ≡ [])
       → (H : (op : Op) → (ε'' : E)
            → Γ ᴱ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
       → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
       → (uH : EffUniformʰ {Γ} H pH)
       → ∀ {εa εb} → (q : εa ≾ₑ εb)
       → Halg {ε₂ = ε₂} e H pH uH {εb} ∘ᵐ T-≤ q
       ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ Halg e H pH uH {εa}
Halg-≤ {Γ} e H pH uH q =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∅-terminal e _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-≤ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH) q)
  ∙ ∘ᵐ-assoc _ _ _

Halg-η : ∀ {Γ B ε₂} → (e : Γ ᴱ ≡ [])
       → (H : (op : Op) → (ε'' : E)
            → Γ ᴱ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
       → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
       → (uH : EffUniformʰ {Γ} H pH)
       → Halg {ε₂ = ε₂} e H pH uH {uₑ} ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂}
       ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂))
Halg-η {Γ} {B} {ε₂} e H pH uH =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∅-terminal e (term∅ e ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂})
                            (term∅ {X = Tᵒ ⟦ B ⟧ᵛ ε₂} e)
              , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-ηᵀ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-sndᵐ _ _)
  ∙ ∘ᵐ-identityʳ _

-- The handle interpretation collapses to `Halg` applied to the `⨟`-style
-- environment-threading term: the parameter `projᴱ Γ` is replaced by the
-- terminal map (both agree by `∅-terminal`).
handle-collapse : ∀ {Γ A B ε ε₂} → (e : Γ ᴱ ≡ [])
  → (M : Γ ⊢C⦂ A ‼ ε)
  → (H : (op : Op) → (ε'' : E)
       → Γ ᴱ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → (pM : Paramᶜ M) → (pN : Paramᶜ N)
  → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
  → (uH : EffUniformʰ {Γ} H pH)
  → ⟦ handle M `with H `in N ⟧ᶜᵗ (pM , pN , pH , uH)
  ≈ᵐ Halg {ε₂ = ε₂} e H pH uH {ε}
       ∘ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ)
handle-collapse {Γ} e M H N pM pN pH uH =
    ∘ᵐ-congʳ (⟨ ∅-terminal e (projᴱ Γ)
                  (term∅ e ∘ᵐ (Tᶠ (⟦ N ⟧ᶜᵗ pN) ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ))
              , ≈ᵐ-refl ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl , ≈ᵐ-sym (∘ᵐ-identityˡ _) ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)

-- Box-level terminality of `⟦ Γ ᴱ ⟧` (transport the empty-restriction fact into
-- the box, then use `[]-𝟙-unique`), and extensionality for maps into a boxed
-- product (from `[]-monoidal-η`). These discharge the `necᵉ`-bridge in the
-- handler's delay law when the eternal parameter is trivial.
∅-box-terminal : ∀ {Γ X ρ} → (e : Γ ᴱ ≡ [])
               → (f g : X →ᵐ [ ρ ]ᵒ ⟦ Γ ᴱ ⟧ᶜᵗˣ) → f ≈ᵐ g
∅-box-terminal {X = X} {ρ = ρ} e =
  subst (λ Δ → (f g : X →ᵐ [ ρ ]ᵒ ⟦ Δ ⟧ᶜᵗˣ) → f ≈ᵐ g) (sym e)
        (λ f g → []-𝟙-unique f g)

box-×-ext : ∀ {A B X ρ} → (f g : X →ᵐ [ ρ ]ᵒ (A ×ᵐ B))
          → [ ρ ]ᶠ fstᵐ ∘ᵐ f ≈ᵐ [ ρ ]ᶠ fstᵐ ∘ᵐ g
          → [ ρ ]ᶠ sndᵐ ∘ᵐ f ≈ᵐ [ ρ ]ᶠ sndᵐ ∘ᵐ g
          → f ≈ᵐ g
box-×-ext f g pf ps =
    ≈ᵐ-sym (∘ᵐ-identityˡ _)
  ∙ ∘ᵐ-congˡ (≈ᵐ-sym []-monoidal-η)
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ pf , ps ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (⟨⟩ᵐ-∘ _ _ _))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ []-monoidal-η
  ∙ ∘ᵐ-identityˡ _

Halg-delay : ∀ {Γ B ε₂} → (e : Γ ᴱ ≡ [])
       → (H : (op : Op) → (ε'' : E)
            → Γ ᴱ ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
              ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
       → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
       → (uH : EffUniformʰ {Γ} H pH)
       → ∀ {ε'} → (τ : ℕ)
       → Halg {ε₂ = ε₂} e H pH uH {of-natᵉ τ ·ₑ ε'} ∘ᵐ delayᵀ τ
       ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
           ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (Halg e H pH uH {ε'})
Halg-delay {Γ} e H pH uH τ =
    ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ _)
  ∙ ∘ᵐ-congʳ (⟨ ∅-terminal e _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong)
  ∙ ∘ᵐ-congʳ (≈ᵐ-sym (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ∘ᵐ-identityʳ _ ⟩ᵐ-cong))
  ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congˡ (T-alg-of-handlerᵀ-delayᵀ τ (bcᴱ Γ) (⟦_⟧ʰᵗ {Γ} H pH uH))
  ∙ ∘ᵐ-assoc _ _ _
  ∙ ∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ necbridge))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym ([]-∘ᵐ _ _)))
  where
    necbridge : []-monoidal ∘ᵐ mapˣᵐ (Eternalᵒ.necᵉ (bcᴱ Γ) {of-natʳ τ}) idᵐ
                  ∘ᵐ ⟨ term∅ e , idᵐ ⟩ᵐ
              ≈ᵐ [ of-natʳ τ ]ᶠ ⟨ term∅ e , idᵐ ⟩ᵐ
    necbridge = box-×-ext _ _
      (∅-box-terminal e _ _)
      (   ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ ∘ᵐ-congˡ []-monoidal-sndᵐ
        ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
        ∙ ∘ᵐ-congˡ (⟨⟩ᵐ-sndᵐ _ _)
        ∙ ∘ᵐ-congˡ (∘ᵐ-identityˡ _)
        ∙ ⟨⟩ᵐ-sndᵐ _ _
        ∙ ≈ᵐ-sym (≈ᵐ-sym ([]-∘ᵐ _ _) ∙ []-congᶠ (⟨⟩ᵐ-sndᵐ _ _) ∙ []-idᵐ))

-- The operation law of the collapsed handler algebra, imported from the
-- abstract `HandlerAlgebra` module (instantiated at the terminal parameter
-- `⟦ Γ ᴱ ⟧`). This is the fold's operation law with the parameter-free clause.
Halg-op : ∀ {Γ B ε ε'} → (e : Γ ᴱ ≡ [])
        → (H : (op : Op) → (ε'' : E)
             → Γ ᴱ ∷ type-of-gtype (param op)
                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
               ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
        → (uH : EffUniformʰ {Γ} H pH)
        → (op : Op)
        → Halg {ε₂ = ε'} e H pH uH {op-grade op ·ₑ ε} ∘ᵐ opᵀ {ε = ε} op
        ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (op-grade op) ε ε'))
           ∘ᵐ (clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op (ε ·ₑ ε') ∘ᵐ ⟨ term∅ e , idᵐ ⟩ᵐ)
           ∘ᵐ mapˣᵐ idᵐ ([ mapᵉ (op-grade op) ]ᶠ (map⇒ᵐ idᵐ (Halg e H pH uH {ε})))
Halg-op {Γ} e H pH uH op =
  HC.Halg-op Mon (bcᴱ Γ) (term∅ e) (∅-terminal e) (∅-box-terminal e)
             (⟦_⟧ʰᵗ {Γ} H pH uH) op

-- HANDLE-STEP
--
-- The same assembly as `SEQ-STEP`, with the handler's fold in place of the
-- monad multiplication. Everything is shared: `seq-step-core`, `step-box` and
-- `seq-target` are all generic in the algebra, and the two laws the chain uses
-- of `μᵀ` (`T-≤-μᵀ`, `T-μ∘μ≡μ∘Tμ`) are matched by the handler's own
-- (`T-alg-of-handlerᵀ-≤`, `T-alg-of-handlerᵀ-μᵀ`).

sound-HANDLE-STEP : ∀ {ε₁ ε₂ ε₃ A B} {S S' : 𝕊 []}
  → {M : toCtx S ⊢C⦂ A ‼ ε₁}
  → (H : (op : Op) → (ε'' : E)
       → toCtx S ᴱ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
  → (N : toCtx S ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
  → {M' : toCtx S' ⊢C⦂ A ‼ ε₃}
  → (r : ⟨ S , M ⟩ ↝ ⟨ S' , M' ⟩)
  → (c : ≤ₛ-grade (step-extends-state r) ·ᵣ mapᵉ ε₃ ≾ᵣ mapᵉ ε₁)
  → (pS : Paramˢ S) → (pM : Paramᶜ M) → (pN : Paramᶜ N) → (pM' : Paramᶜ M')
  → (pH : ∀ op ε'' → Paramᶜ (H op ε''))
  → (uH : EffUniformʰ {toCtx S} H pH)
  → ⟦ M ⟧ᶜᵗ pM ∘ᵐ ⟦ S ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ r)
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ A ⟧ᵛ} {step-grade r} {ε₃}
              (⟦ M' ⟧ᶜᵗ pM' ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM)) (stepᵀ r)
  → ⟦ handle M `with H `in N ⟧ᶜᵗ (pM , pN , pH , uH) ∘ᵐ ⟦ S ⟧ˢ pS
    ≈ᵐ T-≤ (step-≾ (HANDLE-STEP {H = H} {N = N} r c))
       ∘ᵐ _⋄_ {⟦ hist S ⟧ᶜᵗˣ} {⟦ hist S' ⟧ᶜᵗˣ} {⟦ B ⟧ᵛ} {step-grade r} {ε₃ ·ₑ ε₂}
              (⟦ handle M'
                   `with (λ op ε'' →
                            subst
                              (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ]
                                            (type-of-gtype (arity op) ⇒ B ‼ ε'')
                                      ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
                              (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S')))
                              (H op ε''))
                   `in (C-rename (cong-∷-ren
                                   (suc-comp-ren (step-extends-state r) c)) N) ⟧ᶜᵗ
                      (pM'
                      , renᶜ (cong-∷-ren (suc-comp-ren (step-extends-state r) c)) N pN
                      , (λ op ε'' →
                           substᴾᶜ (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S')))
                             (H op ε'') (pH op ε''))
                      , subst-clauses-uniform
                          (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S'))) H pH uH)
                 ∘ᵐ ⟦ S' ⟧ˢ (stepᴾˢ r pS pM))
              (stepᵀ r)
sound-HANDLE-STEP {ε₁} {ε₂} {ε₃} {A} {B} {S} {S'} {M} H N {M'} r c pS pM pN pM' pH uH ih =
    ∘ᵐ-congˡ (handle-collapse eS M H N pM pN pH uH)
  ∙ seq-step-core alg alg-≤ N r c pS (stepᴾˢ r pS pM) pM pN pM' ih
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (⟨ box-merge _ _ (seq-g r) _ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (step-box r c (seq-g r) pS pM))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ
      (∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _ ∙ ⟨ ∘ᵐ-identityˡ _ , ≈ᵐ-refl ⟩ᵐ-cong)))))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _)))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (μᵀ-nat _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-assoc _ _ _))
  -- merge the two functorial actions, so the bind is a single `Tᶠ f`
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (≈ᵐ-sym (∘ᵐ-assoc _ _ _))))
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (≈ᵐ-sym (T-∘ᵐ _ _)))))
  -- THE KEY STEP: the handler commutes with the step transition, because a
  -- reduction step never performs an operation
  ∙ ∘ᵐ-congʳ (alg-stepᵀ {B = B} alg alg-≤ alg-η alg-delay r _)
  -- drop the identity the strength's pairing picked up
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (∘ᵐ-congʳ (∘ᵐ-congʳ
      (∘ᵐ-congʳ ⟨ ≈ᵐ-refl , ∘ᵐ-identityʳ _ ⟩ᵐ-cong)))))))
  -- what is under it is the target's denotation (the handler collapses back, and
  -- its eternal parameter is reconciled across the step by `Halg-SS'`) …
  ∙ ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ (
      ≈ᵐ-sym (seq-target {ε₁} {ε₂} {ε₃} {A} {B}
                  {toCtx S} {toCtx S'} {⟦ hist S' ⟧ᶜᵗˣ}
                  alg N (suc-comp-ren (step-extends-state r) c) M'
                  (⟦ S' ⟧ˢ (stepᴾˢ r pS pM)) pN pM')
    ∙ ∘ᵐ-congˡ (∘ᵐ-congˡ Halg-SS'
               ∙ ≈ᵐ-sym (handle-collapse eS' M' H'
                          (C-rename (cong-∷-ren
                                      (suc-comp-ren (step-extends-state r) c)) N)
                          pM' (renᶜ (cong-∷-ren
                                      (suc-comp-ren (step-extends-state r) c)) N pN)
                          pH' uH')))))))
  -- … and `seq-coe` fixes the grade
  ∙ seq-coe (step-≾ r) (step-≾ (HANDLE-STEP {H = H} {N = N} r c)) _
  where
    eS  = toCtxᴱ-[] S
    eS' = toCtxᴱ-[] S'

    H' : (op : Op) → (ε'' : E)
       → toCtx S' ᴱ ∷ type-of-gtype (param op)
            ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
         ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')
    H' op ε'' =
      subst
        (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                  ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
                ⊢C⦂ B ‼ (op-grade op ·ₑ ε''))
        (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S')))
        (H op ε'')

    pH' : ∀ op ε'' → Paramᶜ (H' op ε'')
    pH' op ε'' =
      substᴾᶜ (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S'))) (H op ε'') (pH op ε'')

    uH' = subst-clauses-uniform (trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S'))) H pH uH

    f : ⟦ toCtx S' ᴱ ⟧ᶜᵗˣ →ᵐ ⟦ toCtx S ᴱ ⟧ᶜᵗˣ
    f = term∅ eS

    alg : ∀ {ε} → Tᵒ (Tᵒ ⟦ B ⟧ᵛ ε₂) ε →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε₂)
    alg = Halg eS H pH uH

    alg-≤ : ∀ {εa εb} → (q : εa ≾ₑ εb)
          → alg {εb} ∘ᵐ T-≤ q ≈ᵐ T-≤ (·ₑ-monoˡ-≾ₑ q) ∘ᵐ alg {εa}
    alg-≤ q = Halg-≤ eS H pH uH q

    alg-η : alg {uₑ} ∘ᵐ ηᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂}
          ≈ᵐ ε-substᵀ (sym (·ₑ-identityˡ ε₂))
    alg-η = Halg-η eS H pH uH

    alg-delay : ∀ {ε'} → (τ : ℕ)
              → alg {of-natᵉ τ ·ₑ ε'} ∘ᵐ delayᵀ {Tᵒ ⟦ B ⟧ᵛ ε₂} {ε'} τ
              ≈ᵐ ε-substᵀ (sym (·ₑ-assoc (of-natᵉ τ) ε' ε₂))
                  ∘ᵐ delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ (alg {ε'})
    alg-delay τ = Halg-delay eS H pH uH τ

    ⟦H'⟧ʰᵗ-nat : ∀ op ε''
               → clauseᵀ (⟦_⟧ʰᵗ {toCtx S'} H' pH' uH') op ε''
               ≈ᵐ clauseᵀ (⟦_⟧ʰᵗ {toCtx S} H pH uH) op ε'' ∘ᵐ mapˣᵐ f idᵐ
    ⟦H'⟧ʰᵗ-nat op ε'' =
        ∘ᵐ-congˡ step1'
      ∙ ∘ᵐ-assoc _ _ _
      ∙ ∘ᵐ-congʳ (adapt-commute _ _ _)
      ∙ ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
      where
        ptᵥ = type-of-gtype (param op)
        ktᵥ = [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε'')
        D₀ = [] ∷ ptᵥ ∷ ktᵥ
        eq = trans (toCtxᴱ-[] S) (sym (toCtxᴱ-[] S'))
        ⟦eqren⟧≈ : ⟦ eq-ren (cong (_++ᶜ D₀) eq) ⟧ʳ
                 ≈ᵐ mapˣᵐ (mapˣᵐ f idᵐ) idᵐ
        ⟦eqren⟧≈ =
            eq-ren-irr (cong (_++ᶜ D₀) eq) (cong (_∷ ktᵥ) (cong (_∷ ptᵥ) eq))
          ∙ eq-ren-∷ (cong (_∷ ptᵥ) eq)
          ∙ mapˣᵐ-cong
              (eq-ren-∷ eq ∙ mapˣᵐ-cong (∅-terminal eS _ _) ≈ᵐ-refl)
              ≈ᵐ-refl
        step1' : ⟦ H' op ε'' ⟧ᶜᵗ (pH' op ε'')
               ≈ᵐ ⟦ H op ε'' ⟧ᶜᵗ (pH op ε'') ∘ᵐ mapˣᵐ (mapˣᵐ f idᵐ) idᵐ
        step1' = subst-clause-interp eq (H op ε'') (pH op ε'')
               ∙ ∘ᵐ-congʳ ⟦eqren⟧≈

    Halg-SS' : ∀ {ε} → Halg eS H pH uH {ε} ≈ᵐ Halg eS' H' pH' uH' {ε}
    Halg-SS' =
      ≈ᵐ-sym (
          ∘ᵐ-congˡ (T-alg-of-handlerᵀ-natᴾ (bcᴱ (toCtx S)) (bcᴱ (toCtx S'))
                     f (∅-box-terminal eS _ _) (⟦_⟧ʰᵗ {toCtx S} H pH uH)
                     _ ⟦H'⟧ʰᵗ-nat)
        ∙ ∘ᵐ-assoc _ _ _
        ∙ ∘ᵐ-congʳ (mapˣᵐ-∘⟨⟩ _ _ _ _
                    ∙ ⟨ ∅-terminal eS _ _ , ∘ᵐ-identityˡ _ ⟩ᵐ-cong))

-- SEQ-OP
--
-- The operation commuting conversion: sequencing a computation that begins
-- with an operation is the operation with the sequencing pushed into its
-- continuation. This is the content of the algebraicity laws,
-- `opᵀ-algebraicity` for the multiplication and `strᵀ-opᵀ-algebraicity` for the
-- strength. The rule leaves the state alone, so this is a plain equation
-- between the two denotations, in an arbitrary context.
--
-- The strength is where the environment goes: the operation's continuation is
-- boxed (it may run only once `op-grade op` worth of time has passed), so the
-- environment is pushed under that box, which is what `exp-strᵐ` does.

-- Reassociating the operation's arguments.
--
-- `strᵀ-opᵀ-algebraicity` hands the operation back its parameter and pairs the
-- environment with the (boxed) continuation. Applied to an actual `perform`,
-- whose argument is `⟨ env , ⟨ param , cont ⟩ᵐ ⟩ᵐ`, that reshuffle just puts the
-- parameter back in front and leaves the environment sitting next to the
-- continuation, ready to be pushed under its box.

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

-- The environment the operation's continuation receives.
--
-- Under the operation's box the environment has already been transposed once
-- (at `mapᵉ (op-grade op)`) and re-locked by `μ`; the continuation then binds
-- the arity value, so the environment must be weakened past it. Doing that
-- *outside* the second transposition (`_ ∘ᵐ fstᵐ`) and doing it *inside* it
-- (the syntax's `cong-⟨⟩-ren wk-ren`) agree, by naturality of `η⊣`.

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

-- PUSHING THE SEQUENCING UNDER THE OPERATION'S BOX
--
-- This is the heart of `SEQ-OP`. On the left the environment arrives boxed at
-- the *whole* computation's grade `mapᵉ (op-grade op ·ₑ ε)`; `strᵀ-opᵀ-algebra-
-- icity` splits that box with `δ` into `mapᵉ (op-grade op)` (the operation's own
-- delay) and `mapᵉ ε` (the continuation's), pairs the inner half with the boxed
-- continuation via `[]-monoidal`, and pushes it under the exponential with
-- `exp-strᵐ`. On the right the syntax has instead renamed the continuation's
-- context with `⟨⟩-μ-ren`, folding the two locks back into one.
--
-- The two agree: `box-split` is exactly the `δ`-split-then-`μ`-refold, and
-- `η⊣-⟨⟩` is what lets the two transposed halves be re-paired under one box.

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

-- The commuting conversion, at the level of the model.
--
-- The three moves are the operation's three laws: `strᵀ-opᵀ-algebraicity` puts
-- the environment inside the operation's continuation, `opᵀ-nat` puts the
-- sequel `n` there too, and `opᵀ-algebraicity` puts the multiplication there —
-- leaving the `ε-substᵀ` that reassociates the grades, which is exactly the
-- coercion the syntactic rule carries. The ground-type coercion `ea` is
-- generalised so it can be matched, at which point both `subst`s vanish.

seq-op-core : ∀ {X Y A B ε ε'} → (op : Op)
            -- the algebra that collapses the two monad layers (`μᵀ` for `⨟`,
            -- the handler's fold for `handle`) …
            → (alg : ∀ {ε₀} → Tᵒ (Tᵒ B ε') ε₀ →ᵐ Tᵒ B (ε₀ ·ₑ ε'))
            -- … and what it does to an operation: re-emit it (`opᵀ-algebraicity`)
            -- or apply the matching clause (`T-alg-of-handlerᵀ-opᵀ`). Either way
            -- the algebra is pushed into the operation's continuation.
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

gty-cancelᶜ : ∀ {Z W Y Y'} → (e : Y ≡ Y') → (f : (Z ×ᵐ Y) →ᵐ W)
            → subst (λ O → (Z ×ᵐ O) →ᵐ W) e f
                ∘ᵐ mapˣᵐ idᵐ (subst (λ O → O →ᵐ Y') (sym e) idᵐ)
            ≈ᵐ f
gty-cancelᶜ refl f = ∘ᵐ-congʳ mapˣᵐ-idᵐ ∙ ∘ᵐ-identityʳ _

-- The codomain counterpart of `gty-cancelᶜ`: a codomain coercion and its inverse
-- cancel. Used where the `handle-perform` reduct's parameter coercion meets its
-- inverse from `⟦_⟧ʰᵗ`.
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

-- HANDLE-OP
--
-- Handling an operation applies the matching clause, with the rest of the
-- handled computation boxed up as the clause's continuation, the box being what
-- stops the continuation running before `op-grade op` worth of time has passed.
-- So the reduct is a `box`, and the equation is `SEQ-OP`'s with the handler's
-- fold in place of the monad multiplication: `T-alg-of-handlerᵀ-opᵀ` (apply a
-- clause) where `SEQ-OP` has `opᵀ-algebraicity` (re-emit the operation).
--
-- HANDLE-OP: the operation is handled by its clause, with the rest of the
-- computation boxed up as the clause's continuation.

sound-HANDLE-OP : ∀ {Γ A B ε ε''} → (e : Γ ᴱ ≡ []) → (op : Op)
                → (V : Γ ⊢V⦂ type-of-gtype (param op))
                → (M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                       ⊢C⦂ A ‼ ε)
                → (H : (op' : Op) → (ε' : E)
                     → Γ ᴱ ∷ type-of-gtype (param op')
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
                                              (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                                                       (type-of-gtype (arity op)))))
                                              (H op' ε'))
                                   `in (C-rename (cong-∷-ren
                                          ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren)
                                           ∘ʳ cong-⟨⟩-ren wk-ren)) N)))
                            (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren Γ)))
                                       (H op (ε ·ₑ ε''))
                             [ Tl-∷ Hd ↦ V ]c) ⟧ᶜᵗ
                     ( (pM
                       , renᶜ (cong-∷-ren ((eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren)) N pN
                       , (λ op' ε' →
                            renᶜ (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op))))) (H op' ε') (pH op' ε'))
                       , ren-clauses-uniform
                           (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op)))
                           H pH uH)
                     , subᶜ (C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren Γ)))
                                     (H op (ε ·ₑ ε'')))
                            (Tl-∷ Hd) V
                            (renᶜ (cong-∷-ren (cong-∷-ren (ᴱ-ren Γ)))
                                  (H op (ε ·ₑ ε'')) (pH op (ε ·ₑ ε'')))
                            pV )
sound-HANDLE-OP {Γ} {A} {B} {ε} {ε''} e op V M H N pV pM pN pH uH =
  -- collapse the eternal parameter (`Γ ᴱ ≡ []`), then the commuting conversion
  -- with the handler's fold as the algebra: the operation is algebraic for it
  -- too, and applies a clause
    handle-collapse e (perform op V M) H N (pV , pM) pN pH uH
  ∙ seq-op-core op (Halg {ε₂ = ε''} e H pH uH)
      (clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op (ε ·ₑ ε'') ∘ᵐ ⟨ term∅ e , idᵐ ⟩ᵐ)
      (Halg-op e H pH uH op) (ty-gty (arity op))
      (subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV))
      (⟦ M ⟧ᶜᵗ pM) (⟦ N ⟧ᶜᵗ pN) ⟦ ren ⟧ʳ ern
  -- what is left is the reduct: the clause fired at `Γ`, applied to the
  -- parameter and to the boxed continuation the `box` allocates
  ∙ ∘ᵐ-congʳ tgt
  where
    -- the clause, included from `Γ ᴱ` into the handling context `Γ`
    Hwk = C-rename (cong-∷-ren (cong-∷-ren (ᴱ-ren Γ))) (H op (ε ·ₑ ε''))
    pHwk = renᶜ (cong-∷-ren (cong-∷-ren (ᴱ-ren Γ)))
                (H op (ε ·ₑ ε'')) (pH op (ε ·ₑ ε''))

    ren : Ren [] ((Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ⟨ mapᵉ ε ⟩)
                 (Γ ⟨ mapᵉ (op-grade op ·ₑ ε) ⟩)
    ren = (eq-ren (cong (Γ ⟨_⟩) map-·ᵉ) ∘ʳ ⟨⟩-μ-ren) ∘ʳ cong-⟨⟩-ren wk-ren

    ern : ⟦ ren ⟧ʳ ≈ᵐ ⟨⟩-≤ (≾ᵣ-reflexive (sym map-·ᵉ)) ∘ᵐ μ ∘ᵐ ⟨ mapᵉ ε ⟩ᶠ fstᵐ
    ern = ∘ᵐ-congˡ (∘ᵐ-congˡ (eq-ren-grade map-·ᵉ)) ∙ ∘ᵐ-assoc _ _ _

    -- the box the reduct allocates is the operation's continuation: the
    -- handled remainder, abstracted over the arity value. The `map⇒ᵐ` the
    -- semantic handler applies is undone by `map⇒ᵐ-curryᵐˡ`, and the arity
    -- coercions cancel.
    tgt : (clauseᵀ (⟦_⟧ʰᵗ {Γ} H pH uH) op (ε ·ₑ ε'') ∘ᵐ ⟨ term∅ e , idᵐ ⟩ᵐ)
            ∘ᵐ ⟨ subst (λ O → ⟦ Γ ⟧ᶜᵗˣ →ᵐ O) (ty-gty (param op)) (⟦ V ⟧ᵛᵗ pV)
               , [ mapᵉ (op-grade op) ]ᶠ
                   (curryᵐ (subst (λ O → (⟨ mapᵉ (op-grade op) ⟩ᵒ ⟦ Γ ⟧ᶜᵗˣ ×ᵐ O)
                                         →ᵐ Tᵒ ⟦ B ⟧ᵛ (ε ·ₑ ε''))
                                  (ty-gty (arity op))
                                  (Halg {ε₂ = ε''} e H pH uH
                                     ∘ᵐ Tᶠ (⟦ N ⟧ᶜᵗ pN ∘ᵐ mapˣᵐ ⟦ ren ⟧ʳ idᵐ)
                                     ∘ᵐ strᵀ ∘ᵐ ⟨ η⊣ , ⟦ M ⟧ᶜᵗ pM ⟩ᵐ)))
                 ∘ᵐ η⊣ ⟩ᵐ
        ≈ᵐ ⟦ box (lam (handle M
                        `with (λ op' ε' →
                                 C-rename (cong-∷-ren (cong-∷-ren
                                   (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩}
                                            (type-of-gtype (arity op)))))
                                   (H op' ε'))
                        `in (C-rename (cong-∷-ren ren) N)))
                 (Hwk [ Tl-∷ Hd ↦ V ]c) ⟧ᶜᵗ
             ( (pM
               , renᶜ (cong-∷-ren ren) N pN
               , (λ op' ε' → renᶜ (cong-∷-ren (cong-∷-ren (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op))))) (H op' ε') (pH op' ε'))
               , ren-clauses-uniform
                   (ren-ᴱ-∷ {Γ ⟨ mapᵉ (op-grade op) ⟩} (type-of-gtype (arity op)))
                   H pH uH)
             , subᶜ Hwk (Tl-∷ Hd) V pHwk pV )
    tgt =
        ≈ᵐ-sym (clause-sound e op H pH uH V pV _)
      ∙ ∘ᵐ-congʳ (⟨ ≈ᵐ-refl
          , ≈ᵐ-sym (∘ᵐ-assoc _ _ _)
            ∙ ∘ᵐ-congˡ (≈ᵐ-sym ([]-∘ᵐ _ _))
            -- undo the semantic handler's arity coercion …
            ∙ ∘ᵐ-congˡ ([]-congᶠ (map⇒ᵐ-curryᵐˡ _ _))
            -- … which cancels the interpretation's own
            ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong (gty-cancelᶜ (ty-gty (arity op)) _)))
            -- and what is boxed is the handled remainder (the renamed inner
            -- handle collapses back by `handle-op-cont`)
            ∙ ∘ᵐ-congˡ ([]-congᶠ (curryᵐ-cong
                (≈ᵐ-sym (handle-op-cont e H M N ren pM pN pH uH))))
          ⟩ᵐ-cong)

