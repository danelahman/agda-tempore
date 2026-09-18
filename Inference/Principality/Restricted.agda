------------------------------------------------------------------
-- Principal types on a fragment                                 --
--                                                                --
-- `Inference.Principality.principal` consumes only a solver's    --
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

open import Inference.Scopes

module Inference.Principality.Restricted (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Inference.Open.Grades   S
open import Inference.Open.Types    S
open import Inference.Open.Contexts S
open import Inference.Open.Subst    S
open import Inference.Open.Hyps     S
open import Inference.Open.Language S

open import Inference.Raw.Syntax S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S
open import Inference.Constraints.Properties   S

open import Inference.Generate     S
open import Inference.Soundness    S
open import Inference.Completeness S
open import Inference.Principality S

open import Inference.Solver.Restricted S

--------------------------------------------------------------
-- The theorem, guarded                                      --
--------------------------------------------------------------

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
