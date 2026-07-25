------------------------------------------------------------------------
-- ADEQUACY of the denotational semantics w.r.t. the operational one.   --
--                                                                    --
-- The converse direction of `↝*-sound`: denotational information is    --
-- reflected back into operational behaviour. Assembled from            --
--                                                                    --
--   * whnf existence            — `Adequacy.Normalization.halts`       --
--     (syntactic; the language has no recursion)                       --
--   * the whnf denotes the source — `↝*-sound` (already proved)         --
--   * head faithfulness         — `Adequacy.HeadFaithful` (model side)  --
--                                                                    --
-- Stated for two programs: `⟦ M ⟧ ≈ᵐ ⟦ N ⟧` implies they halt with the  --
-- same shape, at the same operation, with the same answer. That form    --
-- needs no *definability* — only injectivity of the base constants      --
-- (`BaseFaithful`) — and no exhaustiveness of the head forms.           --
--                                                                    --
-- Scope: the non-top-level machine `↝`, where unhandled operations stop --
-- computing and denotations live in the tree monad `Tᵒ`.                --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

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

import OperationalSemantics.Adequacy.HeadFaithful as HF

module OperationalSemantics.Adequacy.Adequacy
         (Spec : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)) Fut Pst)
         (GTy : GroundTypes Spec Cat Fut)
         (Mon : Monad Spec Cat Fut Pst Adj GTy)
         (GE : GroundEternal Spec Cat Fut Pst Adj GTy)
         -- the two model-side assumptions
         (hf : HF.HeadFaithful  Spec Cat Fut Pst Adj GTy Mon GE)
         (bf : HF.BaseFaithful  Spec Cat Fut Pst Adj GTy Mon GE)
       where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts Spec
open import Syntax.Language Spec
open import Syntax.Types    Spec

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ; ⟦_⟧ᵇ; ⟦_⟧ᵇᶜ)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types    Spec Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts Spec Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms    Spec Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State    Spec Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Soundness.Preservation   Spec Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Adequacy.Evaluation     Spec
open import OperationalSemantics.Adequacy.HeadFaithful   Spec Cat Fut Pst Adj GTy Mon GE
open import OperationalSemantics.Adequacy.Normalization  Spec
open import OperationalSemantics.Adequacy.Reducibility   Spec

open HF.HeadFaithful hf
open HF.BaseFaithful bf

-- THE SAME OBSERVABLE BEHAVIOUR
--
-- Two programs halt alike: whenever one returns so does the other, and
-- whenever one gets stuck on an operation so does the other, on the same
-- operation. Together with `halts` and `⇓-exclusive` this is a biconditional
-- characterisation of the shape.

record Same-whnf {A : VType} {ε : E} (M N : Prog A ε) : Set where

  field

    same-ret : Ret-whnf (⟨ ∅ , M ⟩) → Ret-whnf (⟨ ∅ , N ⟩)

    same-op  : (w : Op-whnf (⟨ ∅ , M ⟩))
             → Σ[ w' ∈ Op-whnf (⟨ ∅ , N ⟩) ] Op-whnf.oper w ≡ Op-whnf.oper w'

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- SOUNDNESS, PACKAGED. A program is its whnf, run after the run's transition
  -- and coerced back to the program's grade: `↝*-sound` at the empty state
  -- (`hist ∅ ≡ []`, so `⟦ [] ⟧ᶜᵗˣ = 𝟙ᵐ`), with the transition recognised as a
  -- delay composite (`stepsᵀ-delays`).

  program-run-sound : ∀ {A ε ε'} {cf' : Config (A ‼ ε')}
                    → (M : Prog A ε) → (pM : Paramᶜ M)
                    → (rs : ⟨ ∅ , M ⟩ ↝* cf')
                    → ⟦ M ⟧ᵖ pM
                    ≈ᵐ delayedᵐ (⟦ cf' ⟧ᶜᶠ (stepsᴾᶜᶠ rs (tt , pM)))
                                (stepsᵀ rs) (steps-≾ rs)

  -- ADEQUACY, CASE-FAITHFULNESS. Equal denotations halt alike.
  --
  -- Given a whnf of `M` (`halts`), `program-run-sound` presents `⟦ M ⟧` in
  -- head form; `halts` presents `⟦ N ⟧` likewise; `ret≢op` rules out the
  -- mismatched pairing and `op-inj` identifies the operation.

  adequacy : ∀ {A ε} → {M N : Prog A ε}
           → (pM : Paramᶜ M) → (pN : Paramᶜ N)
           → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
           ----------------------------
           → Same-whnf M N

  -- ADEQUACY AT BASE TYPE. The returned answers are the *same constant*: a
  -- base-typed value over a state context is a constant (`base-canonical`),
  -- `leaf-const` identifies the two denotations, and `const-inj` reflects that
  -- to the syntax.

  adequacy-base : ∀ {b ε} → {M N : Prog (Base b) ε}
                → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
                → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
                ------------------------------------------------------------
                → Σ[ c ∈ BaseConstants b ]
                    (Ret-whnf.value wM ≡ const c) × (Ret-whnf.value wN ≡ const c)

  -- THE HYPOTHESIS FORM. A point already presented as a delayed leaf, resp. a
  -- delayed operation node, dictates how the program halts. (No exhaustiveness
  -- of head forms is claimed — only that a *given* head form is realised.)

  leaf-adequacy : ∀ {A ε Y δ n} → {M : Prog A ε} → (pM : Paramᶜ M)
                → {a : Y →ᵐ ⟦ A ⟧ᵛ}
                → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
                → (r : δ ·ₑ uₑ ≾ₑ ε)
                → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r
                -------------------------------------
                → Ret-whnf (⟨ ∅ , M ⟩)

  node-adequacy : ∀ {A ε ε₂ Y δ n op} → {M : Prog A ε} → (pM : Paramᶜ M)
                → {w : Y →ᵐ ⟦ param op ⟧ᵍ}
                → {k : Y →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)}
                → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
                → (r : δ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
                → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ op w k) d r
                ------------------------------------------
                → Σ[ w' ∈ Op-whnf (⟨ ∅ , M ⟩) ] Op-whnf.oper w' ≡ op

  -- THE TIMED REFINEMENT, opt-in: under `HeadTimed` the two programs also take
  -- the same time. Separated because the natural proof of `HeadTimed` needs the
  -- Kripke frame to interpolate a composite step, which fails in general.

  adequacy-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
                 → ∀ {A ε} → {M N : Prog A ε}
                 → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                 → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
                 → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
                 -----------------------------------------------------------
                 → ret-ticks wM ≡ ret-ticks wN

------------------------------------------------------------------------
-- COROLLARIES
------------------------------------------------------------------------

-- Every program halts in exactly one of the two shapes, and equal denotations
-- pick out the same one: if `M` returns then `N` cannot get stuck on an
-- operation.

ret-not-op : ∀ {A ε} → {M N : Prog A ε}
           → (pM : Paramᶜ M) → (pN : Paramᶜ N)
           → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
           → Ret-whnf (⟨ ∅ , M ⟩) → Op-whnf (⟨ ∅ , N ⟩)
           → ⊥
ret-not-op pM pN e wM wN =
  ⇓-exclusive (Same-whnf.same-ret (adequacy pM pN e) wM) wN

-- And the operation a stuck program is stuck on is a denotational invariant.

same-operation : ∀ {A ε} → {M N : Prog A ε}
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
               → (w : Op-whnf (⟨ ∅ , M ⟩)) → (w' : Op-whnf (⟨ ∅ , N ⟩))
               → Op-whnf.oper w ≡ Op-whnf.oper w'
same-operation pM pN e w w' with Same-whnf.same-op (adequacy pM pN e) w
... | w'' , eq = trans eq (proj₁ (op-whnf-unique w'' w'))
