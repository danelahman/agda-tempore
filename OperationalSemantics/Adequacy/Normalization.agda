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

open import OperationalSemantics.Adequacy.Environment    Spec
open import OperationalSemantics.Adequacy.Evaluation     Spec
open import OperationalSemantics.Adequacy.Reducibility   Spec
open import OperationalSemantics.Adequacy.RenEquivalence Spec
open import OperationalSemantics.Adequacy.Slice          Spec
open import OperationalSemantics.Adequacy.SubEquivalence Spec

------------------------------------------------------------------------
-- THE FUNDAMENTAL LEMMA
--
-- Induction on the typing derivation. The computation half is still to come:
-- most of its cases are head expansion off the corresponding rule, `handle`
-- inducts on the scrutinee's `Comp` derivation, and `box` moves the environment
-- along `env-alloc`.
------------------------------------------------------------------------

postulate

  FL-C : ∀ {St Γ A ε} → (γ : Env St Γ) → Rel-Env γ
       → (M : Γ ⊢C⦂ A ‼ ε)
       -------------------------------
       → Comp' A ε St (env-C γ M)

-- The value half. Nothing is asked at a base, unit or empty type; a pair is the
-- pair of the actions; a variable is `env-var`.
--
-- At a lambda the environment moves to the state the Kripke clause offers and
-- gains the argument (`sliceᵉ`, `_∷ᵉ_`) — and that is the whole reason the
-- slice is *recorded* in the environment: the clause supplies no store for the
-- later state, and a recorded slice needs none. The reduct the clause asks for
-- is the action's body up to `_≐ᶜ_`, whence `Comp-≐ᶜ`.

FL-V : ∀ {St Γ A} → (γ : Env St Γ) → Rel-Env γ
     → (V : Γ ⊢V⦂ A)
     -------------------------------
     → Val A St (env-V γ V)

FL-V γ pγ (var f x)  = env-var γ pγ x f
FL-V γ pγ (const c)  = tt
FL-V γ pγ ⋆          = tt
FL-V γ pγ ⦉ V , W ⦊   =
  _ , _ , env-Vˢ-pair γ [] V W , FL-V γ pγ V , FL-V γ pγ W

FL-V {A = A ⇒ (B ‼ ε)} γ pγ (lam M) =
    _ , env-Vˢ-lam γ [] M
  , λ q M₂ eM₂ W pW →
      Comp-≐ᶜ (sub-≐ᶜ Hd (≐ᵛ-refl W) (≐ᶜ-sym eM₂))
              (FL-C (sliceᵉ γ q ∷ᵉ W) (pγ , pW) M)

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
-- `toCtx ∅` has no variables to make reducible (`store-∅`).

normalize : ∀ {A ε} → (M : Prog A ε) → Comp' A ε ∅ M
normalize M = subst (Comp' _ _ ∅) (env-C-id M) (FL-C ⌊ ∅ ⌋ store-∅ M)

-- Hence every closed program reaches a weak head normal form: it returns a
-- value, or it gets stuck on an unhandled operation.

halts : ∀ {A ε} → (M : Prog A ε) → Halts (⟨ ∅ , M ⟩)
halts M = Comp-halts (normalize M)
