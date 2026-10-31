------------------------------------------------------------------------
-- Adequacy for the equational theory.                                --
--                                                                    --
-- Reasoning in the equational theory is observationally valid: a     --
-- derivation `[] ⊢ᶜ⦂ M ≡ᵗʰ N` between closed programs denotes an     --
-- equality of global points (`soundᶜ`), and `adequacy` reads that    --
-- back off the machine: the two programs halt in the same shape, on  --
-- the same operation, and at an answer type with the same answer     --
-- (the same constant at a base type, the same boolean at `bool`).    --
--                                                                    --
-- The two theorems meet at `⟦ M ⟧ᵖ ≈ᵐ ⟦ N ⟧ᵖ`; everything here is    --
-- their composition.                                                 --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (inj₁; inj₂)

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

import MonomorphicCalculus.Adequacy.HeadFaithful as HF

module MonomorphicCalculus.Adequacy.Equational
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

open import MonomorphicCalculus.Syntax.Contexts Spec
open import MonomorphicCalculus.Syntax.Terms    Spec
open import MonomorphicCalculus.Syntax.Types    Spec

open import MonomorphicCalculus.EquationalTheory.EquationalTheory Spec

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open Category Cat
open Monad Mon

open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Types    Spec Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Contexts Spec Cat Fut Pst Adj GTy Mon
open import MonomorphicCalculus.DenotationalSemantics.Interpretation.Terms    Spec Cat Fut Pst Adj GTy Mon GE

open import MonomorphicCalculus.OperationalSemantics.Soundness.Preservation Spec Cat Fut Pst Adj GTy Mon GE
       using (⟦_⟧ᵖ)

open import MonomorphicCalculus.EquationalTheory.Soundness            Spec Cat Fut Pst Adj GTy Mon GE
       using (soundᶜ)
open import MonomorphicCalculus.EquationalTheory.Soundness.Parametric Spec Cat Fut Pst Adj GTy Mon GE
       using (Midᶜ)

open import MonomorphicCalculus.Adequacy.Adequacy                Spec Cat Fut Pst Adj GTy Mon GE hf bf
open import MonomorphicCalculus.OperationalSemantics.Evaluation  Spec
open import MonomorphicCalculus.OperationalSemantics.Termination Spec

-- Soundness of the equational theory, read at closed programs: the two sides
-- of a derivable equation are the same global point of `Tᵒ ⟦ A ⟧ᵛ ε`. This is
-- `soundᶜ` at the empty context, where `⟦_⟧ᶜᵗ` is `⟦_⟧ᵖ`.
--
-- `Midᶜ` supplies the certificates the equation's endpoints leave open (the
-- middle term of a transitivity, the substituted value, ...), and `Paramᶜ` the
-- ones the two programs carry; the denotation does not depend on either
-- (`⟦⟧ᶜᵗ-irr`).

≡ᵗʰ-denotation : ∀ {A ε} → {M N : Closed A ε}
               → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               ---------------------------------------
               → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN

≡ᵗʰ-denotation p mp pM pN = soundᶜ p mp pM pN

-- Provable equals halt alike.

≡ᵗʰ-adequacy : ∀ {A ε} → {M N : Closed A ε}
             → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
             → (pM : Paramᶜ M) → (pN : Paramᶜ N)
             ---------------------------------------
             → Same-whnf M N

≡ᵗʰ-adequacy p mp pM pN = adequacy pM pN (≡ᵗʰ-denotation p mp pM pN)

-- And so do they in the other direction: `_≈ᵐ_` is symmetric, so this needs no
-- appeal to `C-sym`.

≡ᵗʰ-adequacy⁻¹ : ∀ {A ε} → {M N : Closed A ε}
               → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               ---------------------------------------
               → Same-whnf N M

≡ᵗʰ-adequacy⁻¹ p mp pM pN = adequacy pN pM (≈ᵐ-sym (≡ᵗʰ-denotation p mp pM pN))

-- Returning is preserved.

≡ᵗʰ-returns : ∀ {A ε} → {M N : Closed A ε}
            → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
            → (pM : Paramᶜ M) → (pN : Paramᶜ N)
            → Ret-whnf (⟨ ∅ ∣ M ⟩)
            ---------------------------------------
            → Ret-whnf (⟨ ∅ ∣ N ⟩)

≡ᵗʰ-returns p mp pM pN = Same-whnf.same-ret (≡ᵗʰ-adequacy p mp pM pN)

-- One side cannot return while the other gets stuck on an operation.

≡ᵗʰ-ret-not-op : ∀ {A ε} → {M N : Closed A ε}
               → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               → Ret-whnf (⟨ ∅ ∣ M ⟩) → Op-whnf (⟨ ∅ ∣ N ⟩)
               ---------------------------------------------
               → ⊥

≡ᵗʰ-ret-not-op p mp pM pN = ret-not-op pM pN (≡ᵗʰ-denotation p mp pM pN)

-- The operation a program is stuck on is invariant under provable equality.

≡ᵗʰ-same-operation : ∀ {A ε} → {M N : Closed A ε}
                   → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
                   → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                   → (w : Op-whnf (⟨ ∅ ∣ M ⟩)) → (w' : Op-whnf (⟨ ∅ ∣ N ⟩))
                   -----------------------------------------------------------
                   → Op-whnf.oper w ≡ Op-whnf.oper w'

≡ᵗʰ-same-operation p mp pM pN = same-operation pM pN (≡ᵗʰ-denotation p mp pM pN)

-- What a closed base-typed program can be observed to do: return a constant,
-- or get stuck on an operation. Two programs agree on the observation when
-- they halt in the same shape with the same constant, resp. the same
-- operation. A run only refines the whnf's value type, so the returned value
-- is read at the program's type (`ret-value`) and its subsumption spine
-- stripped by `base-val`/`bool-val`.

data Same-answer {b : BaseType} {ε : E} (M N : Closed (Base b) ε) : Set where

  both-ret : (wM : Ret-whnf (⟨ ∅ ∣ M ⟩)) → (wN : Ret-whnf (⟨ ∅ ∣ N ⟩))
           → (c : BaseConstants b)
           → base-val (ret-value wM) ≡ const b c
           → base-val (ret-value wN) ≡ const b c
           → Same-answer M N

  both-op  : (wM : Op-whnf (⟨ ∅ ∣ M ⟩)) → (wN : Op-whnf (⟨ ∅ ∣ N ⟩))
           → Op-whnf.oper wM ≡ Op-whnf.oper wN
           → Same-answer M N

-- Derivable equations are observational equations: `halts` supplies a whnf on
-- each side, `≡ᵗʰ-ret-not-op` rules out the mismatched pairings, and the
-- matching ones are `adequacy-base` resp. `same-operation`. No halting
-- hypothesis is needed: every program halts.

≡ᵗʰ-same-answer : ∀ {b ε} → {M N : Closed (Base b) ε}
                → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
                → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                ---------------------------------------
                → Same-answer M N

≡ᵗʰ-same-answer {M = M} {N = N} p mp pM pN = go (halts M) (halts N)
  where
    e : ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
    e = ≡ᵗʰ-denotation p mp pM pN

    go : Halts (⟨ ∅ ∣ M ⟩) → Halts (⟨ ∅ ∣ N ⟩) → Same-answer M N
    go (halts-ret wM) (halts-ret wN) with adequacy-base pM pN e wM wN
    ... | c , sM , sN = both-ret wM wN c sM sN
    go (halts-ret wM) (halts-op wN)  = ⊥-elim (ret-not-op pM pN e wM wN)
    go (halts-op wM)  (halts-ret wN) = ⊥-elim (ret-not-op pN pM (≈ᵐ-sym e) wN wM)
    go (halts-op wM)  (halts-op wN)  = both-op wM wN (same-operation pM pN e wM wN)

-- The same at `bool`, where the returned answer is one of the two constants
-- rather than an element of a base signature.

data Same-answer-bool {ε : E} (M N : Closed bool ε) : Set where

  both-true  : (wM : Ret-whnf (⟨ ∅ ∣ M ⟩)) → (wN : Ret-whnf (⟨ ∅ ∣ N ⟩))
             → bool-val (ret-value wM) ≡ true
             → bool-val (ret-value wN) ≡ true
             → Same-answer-bool M N

  both-false : (wM : Ret-whnf (⟨ ∅ ∣ M ⟩)) → (wN : Ret-whnf (⟨ ∅ ∣ N ⟩))
             → bool-val (ret-value wM) ≡ false
             → bool-val (ret-value wN) ≡ false
             → Same-answer-bool M N

  both-op    : (wM : Op-whnf (⟨ ∅ ∣ M ⟩)) → (wN : Op-whnf (⟨ ∅ ∣ N ⟩))
             → Op-whnf.oper wM ≡ Op-whnf.oper wN
             → Same-answer-bool M N

≡ᵗʰ-same-answer-bool : ∀ {ε} → {M N : Closed bool ε}
                     → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
                     → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                     ---------------------------------------
                     → Same-answer-bool M N

≡ᵗʰ-same-answer-bool {M = M} {N = N} p mp pM pN = go (halts M) (halts N)
  where
    e : ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
    e = ≡ᵗʰ-denotation p mp pM pN

    go : Halts (⟨ ∅ ∣ M ⟩) → Halts (⟨ ∅ ∣ N ⟩) → Same-answer-bool M N
    go (halts-ret wM) (halts-ret wN) with adequacy-bool pM pN e wM wN
    ... | inj₁ (sM , sN) = both-true  wM wN sM sN
    ... | inj₂ (sM , sN) = both-false wM wN sM sN
    go (halts-ret wM) (halts-op wN)  = ⊥-elim (ret-not-op pM pN e wM wN)
    go (halts-op wM)  (halts-ret wN) = ⊥-elim (ret-not-op pN pM (≈ᵐ-sym e) wN wM)
    go (halts-op wM)  (halts-op wN)  = both-op wM wN (same-operation pM pN e wM wN)

-- Opt-in, as in `adequacy-ticks`: under `HeadTimed` provably equal programs
-- also take the same time to return.

≡ᵗʰ-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
          → ∀ {A ε} → {M N : Closed A ε}
          → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
          → (pM : Paramᶜ M) → (pN : Paramᶜ N)
          → (wM : Ret-whnf (⟨ ∅ ∣ M ⟩)) → (wN : Ret-whnf (⟨ ∅ ∣ N ⟩))
          -------------------------------------------------------------
          → ret-ticks wM ≡ ret-ticks wN

≡ᵗʰ-ticks ht p mp pM pN = adequacy-ticks ht pM pN (≡ᵗʰ-denotation p mp pM pN)
