------------------------------------------------------------------
-- Principal types on a fragment                                 --
--                                                                --
-- `TypeInference.Principality.principal` consumes only a solver's    --
-- soundness and principality, so it transcribes verbatim to a    --
-- `SolverOn` once the guard is threaded: a constraint in the     --
-- fragment that the solver accepts has a principal type.          --
--                                                                --
-- `principal-inst`, the instance reading, applies to the result   --
-- unchanged — it is a property of `Principal`, not of the solver  --
-- that produced it.                                               --
------------------------------------------------------------------

open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Principality.Restricted (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades   S
open import TypeInference.OpenSyntax.Types    S
open import TypeInference.OpenSyntax.Contexts S
open import TypeInference.OpenSyntax.Subst    S
open import TypeInference.OpenSyntax.Hyps     S
open import TypeInference.OpenSyntax.Language S

open import TypeInference.Raw.Syntax S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S
open import TypeInference.Constraints.Properties   S

open import TypeInference.Generate     S
open import TypeInference.Soundness    S
open import TypeInference.Completeness S
open import TypeInference.Principality S

open import TypeInference.Solver.Restricted S

principal-on : ∀ {Pᶜ Pᵖ : ∀ {Θ} → Constraint Θ → Set} → (sv : SolverOn Pᶜ Pᵖ)
             → ∀ {Θ n} → (Γ : OCtx Θ n) → (M : RawC n)
             → Pᵖ C[ Γ , M ]
             → {Θ' : Scope} {σ : Subst (Θ +ty +e) Θ'} {Q : Hyps Θ'}
             → SolverOn.solve sv C[ Γ , M ] ≡ just (Θ' , σ , Q)
             ------------------------------------------------
             → Principal Γ M

principal-on sv {Θ} Γ M p {Θ'} {σ} {Q} eq = mkPrincipal
  Θ' σ Q
  (proj₁ elab) (proj₂ elab)
  (λ δ Q' h → soundC (Γ₊ Γ) M (X̂ Θ) (t̂ Θ) (⊨-mono h C[ Γ , M ] sat))
  (λ σ' Q' D e aeq le →
     SolverOn.solve-principal sv C[ Γ , M ] p eq σ' Q'
       (subst (λ N → σ' ⊨[ Q' ] genC (Γ₊ Γ) N (X̂ Θ ‼ t̂ Θ)) e
              (completeC (Γ₊ Γ) (X̂ Θ) (t̂ Θ) D refl aeq le)))
  where
    sat  = SolverOn.solve-sound sv C[ Γ , M ] eq
    elab = soundC (Γ₊ Γ) M (X̂ Θ) (t̂ Θ) sat
