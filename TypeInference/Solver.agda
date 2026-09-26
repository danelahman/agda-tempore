------------------------------------------------------------------
-- The constraint solver, axiomatised                           --
--                                                              --
-- `Solver` is an assumption, not a construction: `∀ᵉ` and      --
-- `⋀ᵒᵖ` are infinitary, and `∀ᵉ` requires an eigenvariable     --
-- treatment.                                                   --
--                                                              --
-- A solution is a substitution together with a residual        --
-- hypothesis set, itself a context of the open judgement, and  --
-- with obligations, the deferred rigid conditions; the         --
-- substitution solves the constraint at every instance meeting --
-- both. Principality is semantic, as in HM(X): it holds at     --
-- each closed instance.                                        --
--                                                              --
-- The outcome is a solution, a refutation, or stuck            --
-- (`TypeInference.Outcome`). Soundness and principality        --
-- concern solutions, and refutation concerns refutations;      --
-- nothing is claimed of a stuck constraint.                    --
--                                                              --
-- "Residual constraint" is the term of OutsideIn(X)            --
-- (Vytiniotis et al., JFP 2011); cf. Pretnar, Inferring        --
-- Algebraic Effects (LMCS 2014).                               --
------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes
open import TypeInference.Outcome

module TypeInference.Solver (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Types S
open import TypeInference.OpenSyntax.Subst S
open import TypeInference.OpenSyntax.Hyps  S
open import TypeInference.OpenSyntax.Instances S using (Obligs; Satisfiable; _⊨_∣_)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

-- Refutation is stated relative to satisfiable conditions, those that
-- some closed instance satisfies (`Satisfiable`).

record Solver : Set₁ where
  field

    -- A solution is a scope, a substitution into it, and the
    -- hypotheses and obligations left over.

    solve : ∀ {Θ} → Constraint Θ
          → Outcome (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ' × Obligs Θ'))

    -- A solution solves the constraint

    solve-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {R : Obligs Θ'}
                → solve C ≡ solved (Θ' , σ , Q , R)
                ---------------------------------
                → σ ⊨[ Q ∣ R ] C

    -- A refutation means there is no solution under satisfiable
    -- conditions

    solve-refutes : ∀ {Θ} → (C : Constraint Θ)
                  → solve C ≡ refuted
                  → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ') → (R : Obligs Θ')
                  → Satisfiable Q R
                  ----------------------------------------------------------
                  → ¬ (σ ⊨[ Q ∣ R ] C)

    -- A solution is the most general one at each closed instance:
    -- every solution, at a closed instance satisfying its conditions,
    -- factors through it, both in the substitution and in the
    -- conditions

    solve-principal : ∀ {Θ} → (C : Constraint Θ)
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺} {R⁺ : Obligs Θ⁺}
                    → solve C ≡ solved (Θ⁺ , σ⁺ , Q⁺ , R⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'') → (R : Obligs Θ'')
                    → σ ⊨[ Q ∣ R ] C
                    → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ R
                    ---------------------------------------------------
                    → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                        (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ R⁺))
