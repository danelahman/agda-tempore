------------------------------------------------------------------
-- The constraint solver, axiomatised                            --
--                                                                --
-- `Solver` is an *assumption*, not a construction: `_≾ᵣ_`/`_≾ₑ_` --
-- are undecidable in the `Grade` interface, `∀ᵉ` and `⋀ᵒᵖ` are   --
-- infinitary, and `∀ᵉ` additionally demands an eigenvariable     --
-- (skolem) treatment — so no solver exists for an arbitrary      --
-- `LanguageSpec`.                                                --
--                                                                --
-- A residual is a `Hyps`, not a leftover `Constraint`: the       --
-- unsolvable atoms are exactly grade orderings and eternality    --
-- atoms, which is what the mirrored judgement consumes as its    --
-- hypothesis set — so a solution-with-residue is already a       --
-- typing context, with no further translation.                   --
--                                                                --
-- `GroundSolver` returns the *witnessing substitution* rather    --
-- than a grounding: the naive bridge from `_⊨ᵍ_` back to         --
-- `_⊨[_]_` is false (ground satisfaction compares               --
-- interpretations, substitution satisfaction compares            --
-- unnormalised grade expressions). Ground semantics is obtained  --
-- on top, from `⊨-ground` of `Inference.Constraints.Ground`.     --
--                                                                --
-- No `Solver → GroundSolver` derivation is offered: a `Solver`'s --
-- residual `Q⁺` need not be satisfiable by any grounding, and    --
-- its `Θ⁺` need not be empty, so the ground case is genuinely a  --
-- separate assumption.                                           --
--                                                                --
-- A solution is a substitution paired with a constraint set      --
-- still to be satisfied: the residual constraint, in             --
-- OutsideIn(X)'s terminology (Vytiniotis et al., JFP 2011) — cf. --
-- the types with constraint sets of Pretnar, Inferring Algebraic --
-- Effects (LMCS 2014).                                           --
------------------------------------------------------------------

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import Inference.Scopes

module Inference.Solver (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Inference.Open.Types S
open import Inference.Open.Subst S
open import Inference.Open.Hyps  S

open import Inference.Constraints.Syntax       S
open import Inference.Constraints.Satisfaction S

--------------------------------------------------------------
-- Solving with a residue                                    --
--------------------------------------------------------------

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

    -- A failure means there is no solution at all

    solve-complete : ∀ {Θ} → (C : Constraint Θ)
                   → solve C ≡ nothing
                   → ∀ {Θ'} → (σ : Subst Θ Θ') → (Q : Hyps Θ')
                   ------------------------------------------
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

--------------------------------------------------------------
-- Solving into the empty scope                              --
--                                                           --
-- A success carries its own soundness witness, so no         --
-- `gsolve-sound` field is needed.                            --
--------------------------------------------------------------

record GroundSolver : Set₁ where
  field

    gsolve : ∀ {Θ} → (C : Constraint Θ)
           → Maybe (Σ[ σ ∈ Subst Θ ∅ˢ ] (σ ⊨[ ∅ᴴ ] C))

    gsolve-complete : ∀ {Θ} → (C : Constraint Θ)
                    → gsolve C ≡ nothing
                    → (σ : Subst Θ ∅ˢ)
                    --------------------
                    → ¬ (σ ⊨[ ∅ᴴ ] C)
