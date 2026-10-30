------------------------------------------------------------------
-- The constraint solver, axiomatised                           --
--                                                              --
-- `Solver` is the interface of a principal solver; `solver` in --
-- `OpenCalculus.Inference.SolverImpl` meets it for an          --
-- enumerated set of operations.                                --
--                                                              --
-- A solution is a substitution together with a residual        --
-- hypothesis set, itself a context of the open judgement, its  --
-- quantified hypotheses the deferred rigid conditions; the     --
-- substitution solves the constraint under it. Principality is --
-- semantic, as in HM(X): it holds at each closed instance.     --
--                                                              --
-- The outcome is a solution, a refutation, or stuck            --
-- (`OpenCalculus.Inference.Outcome`). Soundness and            --
-- principality concern solutions, and refutation concerns      --
-- refutations; nothing is claimed of a stuck constraint.       --
--                                                              --
-- "Residual constraint" is the term of OutsideIn(X)            --
-- (Vytiniotis et al., JFP 2011); cf. Pretnar, Inferring        --
-- Algebraic Effects (LMCS 2014).                               --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import OpenCalculus.Syntax.Scopes
open import OpenCalculus.Inference.Outcome

module OpenCalculus.Inference.Solver (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OpenCalculus.Syntax.Types S
open import OpenCalculus.Syntax.GradeSubstitution S
open import OpenCalculus.Hypotheses  S
open import OpenCalculus.Hypotheses.Instances S using (Satisfiable; _⊨_)

open import OpenCalculus.Inference.Constraints.Syntax       S
open import OpenCalculus.Inference.Constraints.Satisfaction S

-- Refutation is stated relative to satisfiable conditions, those that
-- some closed instance satisfies (`Satisfiable`).

record Solver : Set₁ where
  field

    -- A solution is a scope, a substitution into it, and the
    -- hypotheses left over.

    solve : ∀ {Θ} → Constraint Θ → Outcome (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))

    -- A solution solves the constraint

    solve-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
                → solve C ≡ solved (Θ' , σ , Q)
                ---------------------------------
                → σ ⊨[ Q ] C

    -- A refutation means there is no solution under satisfiable
    -- hypotheses

    solve-refutes : ∀ {Θ} → (C : Constraint Θ)
                  → solve C ≡ refuted
                  → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                  → Satisfiable Q
                  -----------------------------------------
                  → ¬ (σ ⊨[ Q ] C)

    -- A solution is the most general one at each closed instance:
    -- every solution, at a closed instance satisfying its hypotheses,
    -- factors through it, both in the substitution and in the
    -- hypotheses

    solve-principal : ∀ {Θ} → (C : Constraint Θ)
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                    → solve C ≡ solved (Θ⁺ , σ⁺ , Q⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                    → σ ⊨[ Q ] C
                    → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q
                    ---------------------------------------------------
                    → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                        (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺))
