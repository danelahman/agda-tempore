------------------------------------------------------------------
-- The constraint solver, axiomatised                             --
--                                                                --
-- `Solver` is an assumption, not a construction: `∀ᵉ` and        --
-- `⋀ᵒᵖ` are infinitary, and `∀ᵉ` needs an eigenvariable          --
-- treatment.                                                     --
--                                                                --
-- A solution is a substitution paired with a residual hypothesis --
-- set, which is already a context of the mirrored judgement, and --
-- with obligations, deferred rigid conditions: the substitution  --
-- solves the constraint at every instance meeting both.          --
-- Principality is semantic, HM(X)'s: at each closed instance.    --
--                                                                --
-- `Solver` is guarded by two predicates on the constraint,       --
-- making refutation and principality relative to a class of      --
-- constraints — cf. HM(X)'s parameterisation of principality by  --
-- its constraint system (Odersky, Sulzmann, Wehr 1999).          --
-- Soundness stays unguarded. The two guards are separate:        --
-- refutation fails where a decision procedure is incomplete,     --
-- principality where the constraint language is more expressive  --
-- than the residual one.                                         --
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
open import TypeInference.OpenSyntax.Instances S using (Obligs; Satisfiable; _⊨_∣_)

open import TypeInference.Constraints.Syntax       S
open import TypeInference.Constraints.Satisfaction S

-- Refutation is stated against satisfiable conditions, those some
-- closed instance satisfies (`Satisfiable`): under any others every
-- constraint is entailed.

record Solver (Pᶜ Pᵖ : ∀ {Θ} → Constraint Θ → Set) : Set₁ where
  field

    -- A success returns a scope, a substitution into it, and the
    -- hypotheses and obligations left over.

    solve : ∀ {Θ} → Constraint Θ
          → Maybe (Σ[ Θ' ∈ Scope ] (Subst Θ Θ' × Hyps Θ' × Obligs Θ'))

    -- What is returned is a solution, for every constraint

    solve-sound : ∀ {Θ} → (C : Constraint Θ)
                → {Θ' : Scope} {σ : Subst Θ Θ'} {Q : Hyps Θ'} {R : Obligs Θ'}
                → solve C ≡ just (Θ' , σ , Q , R)
                ---------------------------------
                → σ ⊨[ Q ∣ R ] C

    -- On `Pᶜ`, a failure means there is no solution under
    -- satisfiable conditions

    solve-complete : ∀ {Θ} → (C : Constraint Θ) → Pᶜ C
                   → solve C ≡ nothing
                   → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ') → (R : Obligs Θ')
                   → Satisfiable Q R
                   ----------------------------------------------------------
                   → ¬ (σ ⊨[ Q ∣ R ] C)

    -- On `Pᵖ`, what is returned is the most general solution at
    -- each closed instance: every solution, at a closed instance
    -- satisfying its conditions, factors through it, both in the
    -- substitution and in the conditions

    solve-principal : ∀ {Θ} → (C : Constraint Θ) → Pᵖ C
                    → {Θ⁺ : Scope} {σ⁺ : Subst Θ Θ⁺} {Q⁺ : Hyps Θ⁺} {R⁺ : Obligs Θ⁺}
                    → solve C ≡ just (Θ⁺ , σ⁺ , Q⁺ , R⁺)
                    → ∀ {Θ''} → (σ : Subst Θ Θ'') → (Q : Hyps Θ'') → (R : Obligs Θ'')
                    → σ ⊨[ Q ∣ R ] C
                    → (δ₀ : Subst Θ'' ∅ˢ) → δ₀ ⊨ Q ∣ R
                    ---------------------------------------------------
                    → Σ[ δ ∈ Subst Θ⁺ ∅ˢ ]
                        (((σ⁺ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ₀)) × (δ ⊨ Q⁺ ∣ R⁺))
