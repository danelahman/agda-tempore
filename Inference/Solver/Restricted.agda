------------------------------------------------------------------
-- Solving on a fragment                                         --
--                                                                --
-- A concrete solver is rarely complete and rarely principal on   --
-- every constraint, but it can be both on a precisely delimited  --
-- class. `SolverOn` is `Solver` with those two fields guarded by --
-- a predicate on the constraint, making principality relative to --
-- a class of constraints — no direct source, but cf. HM(X)'s     --
-- parameterisation of principality by its constraint system      --
-- (Odersky, Sulzmann, Wehr 1999).                                --
--                                                                --
-- Soundness stays unguarded: an accepting run always returns a    --
-- satisfaction witness, whatever the constraint.                  --
--                                                                --
-- The two guards are separate because they delimit different      --
-- things: refutation fails where a decision procedure is          --
-- incomplete, principality where the constraint language is more  --
-- expressive than the residual one. Instantiating both at the     --
-- trivial predicate recovers `Solver`.                            --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Solver.Restricted (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Inference.Open.Types S
open import Inference.Open.Subst S
open import Inference.Open.Hyps  S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S

open import Inference.Solver S

--------------------------------------------------------------
-- Solving, complete and principal on a fragment             --
--------------------------------------------------------------

record SolverOn (Pᶜ Pᵖ : ∀ {Θ} → Constraint Θ → Set) : Set₁ where
  field

    solve : ∀ {Θ} → Constraint Θ
          → Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))

    -- What is returned is a solution, for every constraint

    solve-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
                → solve C ≡ just (Θ' , σ , Q)
                ------------------------------
                → σ ⊨[ Q ] C

    -- On `Pᶜ`, a failure means there is no solution at all

    solve-complete : ∀ {Θ} → (C : Constraint Θ) → Pᶜ C
                   → solve C ≡ nothing
                   → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                   ------------------------------------------
                   → ¬ (σ ⊨[ Q ] C)

    -- On `Pᵖ`, what is returned is the most general solution

    solve-principal : ∀ {Θ} → (C : Constraint Θ) → Pᵖ C
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                    → solve C ≡ just (Θ⁺ , σ⁺ , Q⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                    → σ ⊨[ Q ] C
                    ---------------------------------------------------
                    → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
                        (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))

--------------------------------------------------------------
-- The unrestricted case                                     --
--------------------------------------------------------------

toSolver : SolverOn (λ _ → ⊤) (λ _ → ⊤) → Solver
toSolver sv = record
  { solve           = SolverOn.solve sv
  ; solve-sound     = SolverOn.solve-sound sv
  ; solve-complete  = λ C → SolverOn.solve-complete sv C tt
  ; solve-principal = λ C → SolverOn.solve-principal sv C tt
  }
