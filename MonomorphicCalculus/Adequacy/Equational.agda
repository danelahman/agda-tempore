------------------------------------------------------------------------
-- Adequacy for the equational theory.                                --
--                                                                    --
-- In a head-faithful and base-faithful model, reasoning in the       --
-- equational theory is observationally valid: a derivation           --
-- `[] ⊢ᶜ⦂ M ≡ᵗʰ N` between closed programs, with certificates,       --
-- denotes an equality of global points (`soundᶜ`), and `adequacy`    --
-- reads that back off the machine: the two programs halt with the    --
-- same outcome, and at an answer type with the same answer (the same --
-- constant at a base type, the same boolean at `bool`).              --
--                                                                    --
-- The two theorems meet at `⟦ M ⟧ᵖ ≈ᵐ ⟦ N ⟧ᵖ`; everything here is    --
-- their composition.                                                 --
------------------------------------------------------------------------

open import Data.Product

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
             → Same-outcome M N

≡ᵗʰ-adequacy p mp pM pN = adequacy pM pN (≡ᵗʰ-denotation p mp pM pN)

-- And so do they in the other direction: `_≈ᵐ_` is symmetric, so this needs no
-- appeal to `C-sym`.

≡ᵗʰ-adequacy⁻¹ : ∀ {A ε} → {M N : Closed A ε}
               → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
               → (pM : Paramᶜ M) → (pN : Paramᶜ N)
               ---------------------------------------
               → Same-outcome N M

≡ᵗʰ-adequacy⁻¹ p mp pM pN = adequacy pN pM (≈ᵐ-sym (≡ᵗʰ-denotation p mp pM pN))

-- However the two halt, they halt with the same outcome: both return, or both
-- get stuck on the same operation.

≡ᵗʰ-same-outcome : ∀ {A ε} → {M N : Closed A ε}
                 → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
                 → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                 → (hM : Halts ∅ M) → (hN : Halts ∅ N)
                 ---------------------------------------
                 → outcome hM ≡ outcome hN

≡ᵗʰ-same-outcome p mp pM pN = same-outcome pM pN (≡ᵗʰ-denotation p mp pM pN)

-- What a closed base-typed program can be observed to do: return a constant,
-- or get stuck on an operation (`base-answer`). Two programs agree on the
-- observation when they halt with the same answer.

Same-answer : ∀ {b ε} → (M N : Closed (Base b) ε) → Set
Same-answer M N =
  Σ[ hM ∈ Halts ∅ M ] Σ[ hN ∈ Halts ∅ N ] base-answer hM ≡ base-answer hN

-- Derivable equations are observational equations: `termination` supplies a
-- halting on each side, and `adequacy-base` compares the two. No halting
-- hypothesis is needed: every program halts.

≡ᵗʰ-same-answer : ∀ {b ε} → {M N : Closed (Base b) ε}
                → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
                → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                ---------------------------------------
                → Same-answer M N

≡ᵗʰ-same-answer {M = M} {N = N} p mp pM pN =
    termination M , termination N
  , adequacy-base pM pN (≡ᵗʰ-denotation p mp pM pN) (termination M) (termination N)

-- The same at `bool`, where the returned answer is one of the two booleans
-- rather than an element of a base signature (`bool-answer`).

Same-answer-bool : ∀ {ε} → (M N : Closed bool ε) → Set
Same-answer-bool M N =
  Σ[ hM ∈ Halts ∅ M ] Σ[ hN ∈ Halts ∅ N ] bool-answer hM ≡ bool-answer hN

≡ᵗʰ-same-answer-bool : ∀ {ε} → {M N : Closed bool ε}
                     → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
                     → (pM : Paramᶜ M) → (pN : Paramᶜ N)
                     ---------------------------------------
                     → Same-answer-bool M N

≡ᵗʰ-same-answer-bool {M = M} {N = N} p mp pM pN =
    termination M , termination N
  , adequacy-bool pM pN (≡ᵗʰ-denotation p mp pM pN) (termination M) (termination N)

-- Opt-in, as in `adequacy-ticks`: under `HeadTimed` provably equal programs
-- also take the same time to halt.

≡ᵗʰ-ticks : HF.HeadTimed Spec Cat Fut Pst Adj GTy Mon GE
          → ∀ {A ε} → {M N : Closed A ε}
          → (p : [] ⊢ᶜ⦂ M ≡ᵗʰ N) → (mp : Midᶜ p)
          → (pM : Paramᶜ M) → (pN : Paramᶜ N)
          → (hM : Halts ∅ M) → (hN : Halts ∅ N)
          -------------------------------------
          → halt-ticks hM ≡ halt-ticks hN

≡ᵗʰ-ticks ht p mp pM pN = adequacy-ticks ht pM pN (≡ᵗʰ-denotation p mp pM pN)
