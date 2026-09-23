------------------------------------------------------------------
-- The constraint solver, axiomatised                             --
--                                                                --
-- `Solver` is an assumption, not a construction: `∀ᵉ` and        --
-- `⋀ᵒᵖ` are infinitary, and `∀ᵉ` needs an eigenvariable          --
-- treatment.                                                     --
--                                                                --
-- A solution is a substitution paired with a residual hypothesis --
-- set, which is already a context of the mirrored judgement.     --
-- `GroundSolver` is the separate assumption for ground           --
-- semantics, returning the witnessing substitution.              --
--                                                                --
-- "Residual constraint" is OutsideIn(X)'s term (Vytiniotis et    --
-- al., JFP 2011); cf. Pretnar, Inferring Algebraic Effects (LMCS --
-- 2014).                                                         --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Solver (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Types S
open import TypeInference.OpenSyntax.Subst S
open import TypeInference.OpenSyntax.Hyps  S
open import TypeInference.OpenSyntax.Grounding S using (Grounding; _⊨ᴴ_)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

-- A hypothesis set some grounding satisfies. Under any other set every
-- constraint is entailed, so refutation is stated against these.

Satisfiable : ∀ {Θ} → Hyps Θ → Set
Satisfiable {Θ} Q = Σ[ θ ∈ Grounding Θ ] (θ ⊨ᴴ Q)

record Solver : Set₁ where
  field

    -- A success returns a scope, a substitution into it, and the
    -- hypotheses left over.

    solve : ∀ {Θ} → Constraint Θ
          → Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ'))

    -- What is returned is a solution

    solve-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
                → solve C ≡ just (Θ' , σ , Q)
                ------------------------------
                → σ ⊨[ Q ] C

    -- A failure means there is no solution under a satisfiable
    -- hypothesis set

    solve-complete : ∀ {Θ} → (C : Constraint Θ)
                   → solve C ≡ nothing
                   → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ') → Satisfiable Q
                   -----------------------------------------------------------
                   → ¬ (σ ⊨[ Q ] C)

    -- What is returned is the most general solution: every solution
    -- factors through it, both in the substitution and in the residue

    solve-principal : ∀ {Θ} → (C : Constraint Θ)
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺}
                    → solve C ≡ just (Θ⁺ , σ⁺ , Q⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'')
                    → σ ⊨[ Q ] C
                    ---------------------------------------------------
                    → Σ[ δ ∈ Subst Θ⁺ Θ'' ]
                        (((σ⁺ ⨟ˢ δ) ≐ˢ σ) × (Q ⊩ᴴ Q⁺ [ δ ]))

-- A success carries its own soundness witness, so no `gsolve-sound`
-- field is needed.

record GroundSolver : Set₁ where
  field

    gsolve : ∀ {Θ} → (C : Constraint Θ)
           → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C))

    gsolve-complete : ∀ {Θ} → (C : Constraint Θ)
                    → gsolve C ≡ nothing
                    → (σ : Subst Θ ∅ˢ)
                    --------------------
                    → ¬ (σ ⊨[ ∅ᴴ ] C)
