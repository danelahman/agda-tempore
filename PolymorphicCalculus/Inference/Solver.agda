------------------------------------------------------------------
-- The constraint solver, axiomatised                           --
--                                                              --
-- `Solver` is the interface of a principal solver;             --
-- `SolverImpl.solver` meets it for an enumerated set of        --
-- operations. A solution is a substitution with a residual     --
-- hypothesis set, its quantified hypotheses the deferred rigid --
-- conditions. Principality is semantic: it holds at each       --
-- closed instance. The outcome is a solution, a refutation,    --
-- or stuck (`Outcome`), which claims nothing.                  --
--                                                              --
-- "Residual constraint" is the term of OutsideIn(X).           --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes
open import PolymorphicCalculus.Inference.Outcome

module PolymorphicCalculus.Inference.Solver (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Types S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses  S
open import PolymorphicCalculus.Hypotheses.Instances S using (Satisfiable; _⊨_)

open import PolymorphicCalculus.Inference.Constraints.Syntax       S
open import PolymorphicCalculus.Inference.Constraints.Satisfaction S

-- Refutation is relative to satisfiable conditions (`Satisfiable`)

record Solver : Set₁ where
  field

    -- A solution: a scope, a substitution into it, and the hypotheses left

    solve : ∀ {Θ} → Constraint Θ → Outcome (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))

    -- A solution solves the constraint

    solve-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
                → solve C ≡ solved (Θ' , σ , Q)
                ---------------------------------
                → σ ⊨[ Q ] C

    -- A refutation: no solution under satisfiable hypotheses

    solve-refutes : ∀ {Θ} → (C : Constraint Θ)
                  → solve C ≡ refuted
                  → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                  → Satisfiable Q
                  -----------------------------------------
                  → ¬ (σ ⊨[ Q ] C)

    -- Most general at each closed instance: every solution, at a closed instance
    -- satisfying its hypotheses, factors through it in substitution and hypotheses

    solve-principal : ∀ {Θ} → (C : Constraint Θ)
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                    → solve C ≡ solved (Θ⁺ , σ⁺ , Q⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                    → σ ⊨[ Q ] C
                    → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q
                    ---------------------------------------------------
                    → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                        (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺))
