------------------------------------------------------------------------
-- Adequacy for the equational theory.                                --
--                                                                    --
-- Reasoning in the equational theory is observationally valid: a     --
-- derivation `[] ⊢C⦂ M == N` between closed programs denotes an      --
-- equality of global points (`soundᶜ`), and `adequacy` reads that    --
-- back off the machine — the two programs halt in the same shape, on --
-- the same operation, and at an answer type with the same answer:    --
-- the same constant at a base type, the same boolean at `Bool`.      --
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

open import ClosedCalculus.DenotationalSemantics.Model.Category
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Future
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Past
open import ClosedCalculus.DenotationalSemantics.Model.Modality.Adjunction
open import ClosedCalculus.DenotationalSemantics.Model.GroundTypes
open import ClosedCalculus.DenotationalSemantics.Model.GroundEternal
open import ClosedCalculus.DenotationalSemantics.Model.Monad

import ClosedCalculus.Adequacy.HeadFaithful as HF

module ClosedCalculus.Adequacy.Equational
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

open import ClosedCalculus.Syntax.Contexts Spec
open import ClosedCalculus.Syntax.Terms    Spec
open import Language.Types                 Spec

open import ClosedCalculus.EquationalTheory.EquationalTheory Spec

open import ClosedCalculus.OperationalSemantics.PreservationTheorem Spec
open import ClosedCalculus.OperationalSemantics.State               Spec

open Category Cat
open Monad Mon

open import ClosedCalculus.DenotationalSemantics.Interpretation.Types    Spec Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Contexts Spec Cat Fut Pst Adj GTy Mon
open import ClosedCalculus.DenotationalSemantics.Interpretation.Terms    Spec Cat Fut Pst Adj GTy Mon GE

open import ClosedCalculus.OperationalSemantics.Soundness.Preservation Spec Cat Fut Pst Adj GTy Mon GE
       using (⟦_⟧ᵖ)

open import ClosedCalculus.EquationalTheory.Soundness            Spec Cat Fut Pst Adj GTy Mon GE
       using (soundᶜ)
open import ClosedCalculus.EquationalTheory.Soundness.Parametric Spec Cat Fut Pst Adj GTy Mon GE
       using (Midᶜ)

open import ClosedCalculus.Adequacy.Adequacy      Spec Cat Fut Pst Adj GTy Mon GE hf bf
open import ClosedCalculus.Adequacy.Evaluation    Spec
open import ClosedCalculus.Adequacy.Normalization Spec

-- Soundness of the equational theory, read at closed programs: the two sides
-- of a derivable equation are the same global point of `Tᵒ ⟦ A ⟧ᵛ ε`. This is
-- `soundᶜ` at the empty context, where `⟦_⟧ᶜᵗ` is `⟦_⟧ᵖ`.
--
-- `Midᶜ` supplies the certificates the equation's endpoints leave open (the
-- middle term of a transitivity, the substituted value, ...), and `Paramᶜ` the
-- ones the two programs carry; the denotation does not depend on either
-- (`⟦⟧ᶜᵗ-irr`).

==-denotation : ∀ {A ε} → {M N : Prog A ε}
              → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              ---------------------------------------
              → ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN

==-denotation p mp pM pN = soundᶜ p mp pM pN

-- Provable equals halt alike.

==-adequacy : ∀ {A ε} → {M N : Prog A ε}
            → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
            → (pM : Paramᶜ M) → (pN : Paramᶜ N)
            ---------------------------------------
            → Same-whnf M N

==-adequacy p mp pM pN = adequacy pM pN (==-denotation p mp pM pN)

-- And so do they in the other direction: `_≈ᵐ_` is symmetric, so this needs no
-- appeal to `C-sym`.

==-adequacy⁻¹ : ∀ {A ε} → {M N : Prog A ε}
              → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              ---------------------------------------
              → Same-whnf N M

==-adequacy⁻¹ p mp pM pN = adequacy pN pM (≈ᵐ-sym (==-denotation p mp pM pN))

-- Returning is preserved.

==-returns : ∀ {A ε} → {M N : Prog A ε}
           → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
           → (pM : Paramᶜ M) → (pN : Paramᶜ N)
           → Ret-whnf (⟨ ∅ , M ⟩)
           ---------------------------------------
           → Ret-whnf (⟨ ∅ , N ⟩)

==-returns p mp pM pN = Same-whnf.same-ret (==-adequacy p mp pM pN)

-- One side cannot return while the other gets stuck on an operation.

==-ret-not-op : ∀ {A ε} → {M N : Prog A ε}
              → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
              → (pM : Paramᶜ M) → (pN : Paramᶜ N)
              → Ret-whnf (⟨ ∅ , M ⟩) → Op-whnf (⟨ ∅ , N ⟩)
              ---------------------------------------------
              → ⊥

==-ret-not-op p mp pM pN = ret-not-op pM pN (==-denotation p mp pM pN)

-- The operation a program is stuck on is invariant under provable equality.

==-same-operation : ∀ {A ε} → {M N : Prog A ε}
                  → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
                  → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                  → (w : Op-whnf (⟨ ∅ , M ⟩)) → (w' : Op-whnf (⟨ ∅ , N ⟩))
                  -----------------------------------------------------------
                  → Op-whnf.oper w ≡ Op-whnf.oper w'

==-same-operation p mp pM pN = same-operation pM pN (==-denotation p mp pM pN)

-- What a closed base-typed program can be observed to do: return a constant,
-- or get stuck on an operation. Two programs agree on the observation when
-- they halt in the same shape with the same constant, resp. the same
-- operation. A run only refines the whnf's value type, so the returned value
-- is read at the program's type (`ret-value`) and its subsumption spine
-- stripped by `base-val`/`bool-val`.

data Same-answer {b : BaseType} {ε : E} (M N : Prog (Base b) ε) : Set where

  both-ret : (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
           → (c : BaseConstants b)
           → base-val (ret-value wM) ≡ const c
           → base-val (ret-value wN) ≡ const c
           → Same-answer M N

  both-op  : (wM : Op-whnf (⟨ ∅ , M ⟩)) → (wN : Op-whnf (⟨ ∅ , N ⟩))
           → Op-whnf.oper wM ≡ Op-whnf.oper wN
           → Same-answer M N

-- Derivable equations are observational equations: `halts` supplies a whnf on
-- each side, `==-ret-not-op` rules out the mismatched pairings, and the
-- matching ones are `adequacy-base` resp. `same-operation`. No halting
-- hypothesis is needed — every program halts.

==-same-answer : ∀ {b ε} → {M N : Prog (Base b) ε}
               → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               ---------------------------------------
               → Same-answer M N

==-same-answer {M = M} {N = N} p mp pM pN = go (halts M) (halts N)
  where
    e : ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
    e = ==-denotation p mp pM pN

    go : Halts (⟨ ∅ , M ⟩) → Halts (⟨ ∅ , N ⟩) → Same-answer M N
    go (halts-ret wM) (halts-ret wN) with adequacy-base pM pN e wM wN
    ... | c , sM , sN = both-ret wM wN c sM sN
    go (halts-ret wM) (halts-op wN)  = ⊥-elim (ret-not-op pM pN e wM wN)
    go (halts-op wM)  (halts-ret wN) = ⊥-elim (ret-not-op pN pM (≈ᵐ-sym e) wN wM)
    go (halts-op wM)  (halts-op wN)  = both-op wM wN (same-operation pM pN e wM wN)

-- The same at `Bool`, where the returned answer is one of the two constants
-- rather than an element of a base signature.

data Same-answer-bool {ε : E} (M N : Prog Bool ε) : Set where

  both-true  : (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
             → bool-val (ret-value wM) ≡ true
             → bool-val (ret-value wN) ≡ true
             → Same-answer-bool M N

  both-false : (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
             → bool-val (ret-value wM) ≡ false
             → bool-val (ret-value wN) ≡ false
             → Same-answer-bool M N

  both-op    : (wM : Op-whnf (⟨ ∅ , M ⟩)) → (wN : Op-whnf (⟨ ∅ , N ⟩))
             → Op-whnf.oper wM ≡ Op-whnf.oper wN
             → Same-answer-bool M N

==-same-answer-bool : ∀ {ε} → {M N : Prog Bool ε}
                    → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
                    → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                    ---------------------------------------
                    → Same-answer-bool M N

==-same-answer-bool {M = M} {N = N} p mp pM pN = go (halts M) (halts N)
  where
    e : ⟦ M ⟧ᵖ pM ≈ᵐ ⟦ N ⟧ᵖ pN
    e = ==-denotation p mp pM pN

    go : Halts (⟨ ∅ , M ⟩) → Halts (⟨ ∅ , N ⟩) → Same-answer-bool M N
    go (halts-ret wM) (halts-ret wN) with adequacy-bool pM pN e wM wN
    ... | inj₁ (sM , sN) = both-true  wM wN sM sN
    ... | inj₂ (sM , sN) = both-false wM wN sM sN
    go (halts-ret wM) (halts-op wN)  = ⊥-elim (ret-not-op pM pN e wM wN)
    go (halts-op wM)  (halts-ret wN) = ⊥-elim (ret-not-op pN pM (≈ᵐ-sym e) wN wM)
    go (halts-op wM)  (halts-op wN)  = both-op wM wN (same-operation pM pN e wM wN)

-- Opt-in, as in `adequacy-ticks`: under `HeadTimed` provably equal programs
-- also take the same time to return.

==-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
         → ∀ {A ε} → {M N : Prog A ε}
         → (p : [] ⊢C⦂ M == N) → (mp : Midᶜ p)
         → (pM : Paramᶜ M) → (pN : Paramᶜ N)
         → (wM : Ret-whnf (⟨ ∅ , M ⟩)) → (wN : Ret-whnf (⟨ ∅ , N ⟩))
         -------------------------------------------------------------
         → ret-ticks wM ≡ ret-ticks wN

==-ticks ht p mp pM pN = adequacy-ticks ht pM pN (==-denotation p mp pM pN)
