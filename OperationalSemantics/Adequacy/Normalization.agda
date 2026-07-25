------------------------------------------------------------------------
-- Weak-head normalization: the fundamental lemma.                      --
--                                                                    --
-- The language has no recursion, so termination is entirely syntactic:  --
-- no denotational measure, no well-founded `Tᵒ`-height, no split into   --
-- observable and silent steps. What is needed is reducibility, because  --
-- substitution can grow a term.                                        --
--                                                                    --
-- The `handle` case is an induction on the scrutinee's `Comp`           --
-- derivation: each `HANDLE-OP` consumes one resumption premise.         --
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
  --
  -- Cases: `lam`/`_·_` by `Val`'s arrow clause and head expansion off `APP`;
  -- `_⨟_` by running the head and continuing with `SEQ-RET`/`SEQ-OP`;
  -- `match`/`absurd`/`coerce` by head expansion; `perform` by building
  -- `comp-op`; `handle` by induction on the scrutinee's derivation, firing
  -- `HANDLE-OP` and feeding the resumption into the clause; `box`/`unbox` by
  -- moving along the slice; `delay` by head expansion off `DELAY`.

  FL-V : ∀ {St Γ A} → (γ : Env St Γ) → Rel-Env γ
       → (V : Γ ⊢V⦂ A)
       -------------------------------
       → Val A St (env-V γ V)

  FL-C : ∀ {St Γ A ε} → (γ : Env St Γ) → Rel-Env γ
       → (M : Γ ⊢C⦂ A ‼ ε)
       -------------------------------
       → Comp' A ε St (env-C γ M)

  -- A reducible computation halts: read the whnf off the `Comp` constructor.

  Comp-halts : ∀ {A P ε} {St : 𝕊 []} → {M : toCtx St ⊢C⦂ A ‼ ε}
             → Comp A P ε St M
             -----------------
             → Halts (⟨ St , M ⟩)

------------------------------------------------------------------------
-- COROLLARIES
------------------------------------------------------------------------

-- A closed program is reducible at the empty state: `Γ = []`, `St = ∅`, and
-- `⌊ ∅ ⌋` closes nothing (`Store ∅ ≡ ⊤`).

normalize : ∀ {A ε} → (M : Prog A ε) → Comp' A ε ∅ M
normalize M = subst (Comp' _ _ ∅) (env-C-id M) (FL-C ⌊ ∅ ⌋ tt M)

-- Hence every closed program reaches a weak head normal form: it returns a
-- value, or it gets stuck on an unhandled operation.

halts : ∀ {A ε} → (M : Prog A ε) → Halts (⟨ ∅ , M ⟩)
halts M = Comp-halts (normalize M)
