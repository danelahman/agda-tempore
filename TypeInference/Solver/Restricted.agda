------------------------------------------------------------------
-- Solving on a fragment                                          --
--                                                                --
-- `SolverOn` is `Solver` with its refutation and principality    --
-- fields guarded by a predicate on the constraint, making        --
-- principality relative to a class of constraints — cf. HM(X)'s  --
-- parameterisation of principality by its constraint system      --
-- (Odersky, Sulzmann, Wehr 1999). Soundness stays unguarded.     --
--                                                                --
-- The two guards are separate: refutation fails where a decision --
-- procedure is incomplete, principality where the constraint     --
-- language is more expressive than the residual one. Both at the --
-- trivial predicate recovers `Solver`.                           --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Solver.Restricted (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Types S
open import TypeInference.Open.Subst S
open import TypeInference.Open.Hyps  S

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

open import TypeInference.Solver S

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

toSolver : SolverOn (λ _ → ⊤) (λ _ → ⊤) → Solver
toSolver sv = record
  { solve           = SolverOn.solve sv
  ; solve-sound     = SolverOn.solve-sound sv
  ; solve-complete  = λ C → SolverOn.solve-complete sv C tt
  ; solve-principal = λ C → SolverOn.solve-principal sv C tt
  }
