------------------------------------------------------------------------
-- Weak-head normalization: the fundamental lemma.                    --
--                                                                    --
-- The language has no recursion, so termination is syntactic.        --
-- Reducibility is still needed, since substitution can grow a term.  --
--                                                                    --
-- The `handle` case is an induction on the scrutinee's `Comp`        --
-- derivation: each `HANDLE-OP` consumes one resumption premise.      --
------------------------------------------------------------------------

open import Data.Product
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Normalization (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.Types         Spec

open import OperationalSemantics.Adequacy.Environment  Spec
open import OperationalSemantics.Adequacy.Evaluation   Spec
open import OperationalSemantics.Adequacy.Reducibility Spec
open import OperationalSemantics.Adequacy.Slice        Spec

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- THE FUNDAMENTAL LEMMA (mutual, induction on the typing derivation).
  -- Most cases are head expansion off the corresponding rule; `handle`
  -- inducts on the scrutinee's `Comp` derivation, `box` moves the
  -- environment along `env-alloc`.

  FL-V : ∀ {St Γ A} → (γ : Env St Γ) → Rel-Env γ
       → (V : Γ ⊢V⦂ A)
       -------------------------------
       → Val A St (env-V γ V)

  FL-C : ∀ {St Γ A ε} → (γ : Env St Γ) → Rel-Env γ
       → (M : Γ ⊢C⦂ A ‼ ε)
       -------------------------------
       → Comp' A ε St (env-C γ M)

------------------------------------------------------------------------
-- COROLLARIES
------------------------------------------------------------------------

-- A reducible computation halts: its run *is* the evaluation, and which of the
-- two shapes it halts in is which `Comp` constructor it is. The reducibility
-- of the components plays no part — normalization is all that is read off.

Comp-halts : ∀ {A P ε} {St : 𝕊 []} → {M : toCtx St ⊢C⦂ A ‼ ε}
           → Comp A P ε St M
           -------------------
           → Halts (⟨ St , M ⟩)

Comp-halts (comp-ret rs _)  = halts-ret (ret-whnf _ _ rs)
Comp-halts (comp-op rs _ _) = halts-op (op-whnf _ _ _ _ _ rs)

-- A closed program is reducible at the empty state: `Γ = []`, `St = ∅`, and
-- `⌊ ∅ ⌋` closes nothing (`Store ∅ ≡ ⊤`).

normalize : ∀ {A ε} → (M : Prog A ε) → Comp' A ε ∅ M
normalize M = subst (Comp' _ _ ∅) (env-C-id M) (FL-C ⌊ ∅ ⌋ tt M)

-- Hence every closed program reaches a weak head normal form: it returns a
-- value, or it gets stuck on an unhandled operation.

halts : ∀ {A ε} → (M : Prog A ε) → Halts (⟨ ∅ , M ⟩)
halts M = Comp-halts (normalize M)
