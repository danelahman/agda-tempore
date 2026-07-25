------------------------------------------------------------------------
-- ADEQUACY of the denotational semantics w.r.t. the operational one. --
--                                                                    --
-- The converse direction of `↝*-sound`. Assembled from               --
--                                                                    --
--   * whnf existence  — `Normalization.halts` (syntactic)            --
--   * the whnf denotes the source — `↝*-sound`                       --
--   * head faithfulness — `HeadFaithful` (model side)                --
--                                                                    --
-- Stated for two programs: `⟦ M ⟧ ≈ᵐ ⟦ N ⟧` implies they halt with   --
-- the same shape, at the same operation, with the same answer.       --
--                                                                    --
-- Scope: the machine `↝`, where unhandled operations stop computing  --
-- and denotations live in the tree monad `Tᵒ`.                       --
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

-- SOUNDNESS, PACKAGED. A program is its whnf, run after the run's transition
-- and coerced back to the program's grade: `↝*-sound` at the empty state
-- (`hist ∅ ≡ []`, so `⟦ [] ⟧ᶜᵗˣ = 𝟙ᵐ` and the empty environment is `idᵐ`).

program-run-sound : ∀ {A ε ε'} {cf' : Config (A ‼ ε')}
                  → (M : Prog A ε) → (pM : Paramᶜ M)
                  → (rs : ⟨ ∅ , M ⟩ ↝* cf')
                  → ⟦ M ⟧ᵖ pM
                  ≈ᵐ delayedᵐ (⟦ cf' ⟧ᶜᶠ (stepsᴾᶜᶠ rs (tt , pM)))
                              (stepsᵀ rs) (steps-≾ rs)

program-run-sound M pM rs =
  ≈ᵐ-trans (≈ᵐ-sym (∘ᵐ-identityʳ (⟦ M ⟧ᵖ pM)))
           (↝*-sound rs (tt , pM) (uniform↝* rs (tt , pM)))

-- The two head presentations of a program, read off a whnf it reaches.

ret-presentation : ∀ {A ε} → (M : Prog A ε) → (pM : Paramᶜ M)
                 → (w : Ret-whnf (⟨ ∅ , M ⟩))
                 → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ] Σ[ a ∈ (Y →ᵐ ⟦ A ⟧ᵛ) ]
                   Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ret-ticks w) ]
                   Σ[ r ∈ (δ ·ₑ uₑ ≾ₑ ε) ]
                     (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r)
ret-presentation M pM (ret-whnf St V rs) =
    _ , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs)
        (proj₂ (ret-whnf-shape V _ _)))

op-presentation : ∀ {A ε} → (M : Prog A ε) → (pM : Paramᶜ M)
                → (w : Op-whnf (⟨ ∅ , M ⟩))
                → Σ[ Y ∈ Obj ] Σ[ δ ∈ E ] Σ[ ε₂ ∈ E ]
                  Σ[ v ∈ (Y →ᵐ ⟦ param (Op-whnf.oper w) ⟧ᵍ) ]
                  Σ[ k ∈ (Y →ᵐ [ mapᵉ (op-grade (Op-whnf.oper w)) ]ᵒ
                                 (⟦ arity (Op-whnf.oper w) ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)) ]
                  Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (op-ticks w) ]
                  Σ[ r ∈ (δ ·ₑ (op-grade (Op-whnf.oper w) ·ₑ ε₂) ≾ₑ ε) ]
                    (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ (Op-whnf.oper w) v k) d r)
op-presentation M pM (op-whnf St op ε' W M' rs) =
    _ , _ , _ , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs)
        (proj₂ (proj₂ (op-whnf-shape W M' _ _ _))))

-- Equal denotations cannot halt in different shapes, and when both get stuck
-- it is on the same operation: the two presentations meet at `ret≢op`
-- resp. `op-inj`.

ret-vs-op : ∀ {A ε} → {M N : Prog A ε}
          → (pM : Paramᶜ M) → (pN : Paramᶜ N)
          → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
          → Ret-whnf (⟨ ∅ , M ⟩) → Op-whnf (⟨ ∅ , N ⟩)
          -------------------------------------------
          → ⊥
ret-vs-op {M = M} {N = N} pM pN e wM wN
  with ret-presentation M pM wM | op-presentation N pN wN
... | _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN =
  ret≢op ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))

same-oper : ∀ {A ε} → {M N : Prog A ε}
          → (pM : Paramᶜ M) → (pN : Paramᶜ N)
          → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
          → (wM : Op-whnf (⟨ ∅ , M ⟩)) → (wN : Op-whnf (⟨ ∅ , N ⟩))
          ---------------------------------------------------------
          → Op-whnf.oper wM ≡ Op-whnf.oper wN
same-oper {M = M} {N = N} pM pN e wM wN
  with op-presentation M pM wM | op-presentation N pN wN
... | _ , _ , _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , _ , _ , ndN , rN , eN =
  op-inj ndM ndN rM rN (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))

-- ADEQUACY, CASE-FAITHFULNESS. Equal denotations halt alike: `halts` supplies
-- a whnf on each side, and the two lemmas above exclude the mismatched pairing.

adequacy : ∀ {A ε} → {M N : Prog A ε}
         → (pM : Paramᶜ M) → (pN : Paramᶜ N)
         → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
         ----------------------------
         → Same-whnf M N

adequacy {M = M} {N = N} pM pN e = record { same-ret = sr ; same-op = so }
  where
    sr : Ret-whnf (⟨ ∅ , M ⟩) → Ret-whnf (⟨ ∅ , N ⟩)
    sr wM with halts N
    ... | halts-ret wN = wN
    ... | halts-op wN  = ⊥-elim (ret-vs-op pM pN e wM wN)

    so : (wM : Op-whnf (⟨ ∅ , M ⟩))
       → Σ[ wN ∈ Op-whnf (⟨ ∅ , N ⟩) ] Op-whnf.oper wM ≡ Op-whnf.oper wN
    so wM with halts N
    ... | halts-ret wN = ⊥-elim (ret-vs-op pN pM (≈ᵐ-sym e) wN wM)
    ... | halts-op wN  = wN , same-oper pM pN e wM wN

-- The head presentation at base type, with the constant it returns.

const-presentation : ∀ {b ε} → (M : Prog (Base b) ε) → (pM : Paramᶜ M)
                   → (w : Ret-whnf (⟨ ∅ , M ⟩))
                   → Σ[ c ∈ BaseConstants b ] Σ[ Y ∈ Obj ] Σ[ δ ∈ E ]
                     Σ[ d ∈ (𝟙ᵐ →ᵐ Tᵒ Y δ) ] Σ[ nd ∈ Delaysᵐ d (ret-ticks w) ]
                     Σ[ r ∈ (δ ·ₑ uₑ ≾ₑ ε) ]
                       (Ret-whnf.value w ≡ const c)
                     × (⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ)) d r)

const-presentation M pM (ret-whnf St V rs) with base-leaf-const V _ _
... | c , sc , qc =
    c , _ , _ , _ , stepsᵀ-delays rs , steps-≾ rs , sc
  , ≈ᵐ-trans (program-run-sound M pM rs)
      (delayedᵐ-cong (stepsᵀ rs) (steps-≾ rs) qc)

-- ADEQUACY AT BASE TYPE. The returned answers are the same constant:
-- `leaf-const` identifies the two denotations and `const-inj` reflects that to
-- the syntax.

adequacy-base : ∀ {b ε} → {M N : Prog (Base b) ε}
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
              → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
              ------------------------------------------------------------
              → Σ[ c ∈ BaseConstants b ]
                  (Ret-whnf.value wM ≡ const c) × (Ret-whnf.value wN ≡ const c)

adequacy-base {M = M} {N = N} pM pN e wM wN
  with const-presentation M pM wM | const-presentation N pN wN
... | cM , _ , _ , _ , ndM , rM , sM , eM
    | cN , _ , _ , _ , ndN , rN , sN , eN
  with const-inj (leaf-const ndM ndN rM rN
                    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN)))
... | refl = cM , sM , sN

-- THE HYPOTHESIS FORM. A point presented as a delayed leaf, resp. a delayed
-- operation node, dictates how the program halts.

leaf-adequacy : ∀ {A ε Y δ n} → {M : Prog A ε} → (pM : Paramᶜ M)
              → {a : Y →ᵐ ⟦ A ⟧ᵛ}
              → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ uₑ ≾ₑ ε)
              → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (leafᵐ a) d r
              -------------------------------------
              → Ret-whnf (⟨ ∅ , M ⟩)

leaf-adequacy {M = M} pM nd r eq = go (halts M)
  where
    go : Halts (⟨ ∅ , M ⟩) → Ret-whnf (⟨ ∅ , M ⟩)
    go (halts-ret w) = w
    go (halts-op w) with op-presentation M pM w
    ... | _ , _ , _ , _ , _ , _ , ndO , rO , eO =
      ⊥-elim (ret≢op nd ndO r rO (≈ᵐ-trans (≈ᵐ-sym eq) eO))

node-adequacy : ∀ {A ε ε₂ Y δ n op} → {M : Prog A ε} → (pM : Paramᶜ M)
              → {v : Y →ᵐ ⟦ param op ⟧ᵍ}
              → {k : Y →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε₂)}
              → {d : 𝟙ᵐ →ᵐ Tᵒ Y δ} → Delaysᵐ d n
              → (r : δ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
              → ⟦ M ⟧ᵖ pM ≈ᵐ delayedᵐ (nodeᵐ op v k) d r
              ------------------------------------------
              → Σ[ w' ∈ Op-whnf (⟨ ∅ , M ⟩) ] Op-whnf.oper w' ≡ op

node-adequacy {op = op} {M = M} pM nd r eq = go (halts M)
  where
    go : Halts (⟨ ∅ , M ⟩)
       → Σ[ w' ∈ Op-whnf (⟨ ∅ , M ⟩) ] Op-whnf.oper w' ≡ op
    go (halts-ret w) with ret-presentation M pM w
    ... | _ , _ , _ , _ , ndR , rR , eR =
      ⊥-elim (ret≢op ndR nd rR r (≈ᵐ-trans (≈ᵐ-sym eR) eq))
    go (halts-op w) with op-presentation M pM w
    ... | _ , _ , _ , _ , _ , _ , ndO , rO , eO =
      w , sym (op-inj nd ndO r rO (≈ᵐ-trans (≈ᵐ-sym eq) eO))

-- THE TIMED REFINEMENT, opt-in: under `HeadTimed` the two programs also take
-- the same time. The presentations are indexed by the runs' tick totals, so
-- this is `ret-ticks-eq` at them.

adequacy-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
               → ∀ {A ε} → {M N : Prog A ε}
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
               → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
               -----------------------------------------------------------
               → ret-ticks wM ≡ ret-ticks wN

adequacy-ticks ht {M = M} {N = N} pM pN e wM wN
  with ret-presentation M pM wM | ret-presentation N pN wN
... | _ , _ , _ , _ , ndM , rM , eM
    | _ , _ , _ , _ , ndN , rN , eN =
  HF.HeadTimed.ret-ticks-eq ht ndM ndN rM rN
    (≈ᵐ-trans (≈ᵐ-sym eM) (≈ᵐ-trans e eN))

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
