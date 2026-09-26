------------------------------------------------------------------
-- The constraint language                                      --
--                                                              --
-- A constraint over a scope `Θ` is a first-order formula over  --
-- the open types and grade expressions of `Θ`, built from      --
-- value-type subtyping, grade orderings, eternality atoms,     --
-- var-rule disjunctions, existential quantification over the   --
-- three sorts of variables, a rigid (eigenvariable)            --
-- effect-grade quantifier, and a conjunction indexed by        --
-- operation symbols.                                           --
--                                                              --
-- Computation-type subtyping is not a former: `C ≾̂ᶜ C'` is     --
-- `(A ≾̂ᵥᶜ A') ∧̂ (ε ≾̂ₑᶜ ε')`. A type equation `A ≐ᵥ B` is       --
-- mutual subtyping, `(A ≾̂ᵥᶜ B) ∧̂ (B ≾̂ᵥᶜ A)`; subtyping being   --
-- structural, it fixes the shape and makes the grades and type --
-- variables equal up to mutual ordering.                       --
--                                                              --
-- Constraints with binders follow Pottier and Rémy, The        --
-- Essence of ML Type Inference (ATTAPL, 2005).                 --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

module TypeInference.Constraints.Syntax (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S

-- Constraints

data Constraint (Θ : Scope) : Set where
  ⊤̂     : Constraint Θ                                -- trivially satisfied
  ⊥̂     : Constraint Θ                                -- unsatisfiable
  _∧̂_   : Constraint Θ → Constraint Θ → Constraint Θ  -- conjunction
  _≾̂ᵥᶜ_ : OVType Θ → OVType Θ → Constraint Θ          -- value-type subtyping
  _≾̂ᵣᶜ_ : RExp Θ → RExp Θ → Constraint Θ              -- resource-grade ordering
  _≾̂ₑᶜ_ : EExp Θ → EExp Θ → Constraint Θ              -- effect-grade ordering
  Etᶜ   : OVType Θ → Constraint Θ                     -- eternality of a type
  Et∨≾ᵘ : OVType Θ → RExp Θ → Constraint Θ            -- the `var`-rule disjunction
  ∃ᵗ_   : Constraint (Θ +ty) → Constraint Θ           -- fresh type variable
  ∃ʳ_   : Constraint (Θ +r)  → Constraint Θ           -- fresh resource-grade variable
  ∃ᵉ_   : Constraint (Θ +e)  → Constraint Θ           -- fresh effect-grade variable
  ∀ᵉ_   : Constraint (Θ +e)  → Constraint Θ           -- rigid effect-grade variable
  ⋀ᵒᵖ   : (Op → Constraint Θ) → Constraint Θ          -- conjunction over operations

-- A type equation

_≐ᵥ_ : ∀ {Θ} → OVType Θ → OVType Θ → Constraint Θ
A ≐ᵥ B = (A ≾̂ᵥᶜ B) ∧̂ (B ≾̂ᵥᶜ A)

infixr 6 _∧̂_
infix  4 _≐ᵥ_ _≾̂ᵥᶜ_ _≾̂ᵣᶜ_ _≾̂ₑᶜ_
infix  2 ∃ᵗ_ ∃ʳ_ ∃ᵉ_ ∀ᵉ_

-- Binders are traversed with the lifts `_↑ᵗ`/`_↑ʳ`/`_↑ᵉ` of
-- `TypeInference.OpenSyntax.Subst`; weakening is a substitution
-- like any other.

infixl 50 _[_]ᶜⁿ

_[_]ᶜⁿ : ∀ {Θ Θ'} → Constraint Θ → Subst Θ Θ' → Constraint Θ'
⊤̂           [ σ ]ᶜⁿ = ⊤̂
⊥̂           [ σ ]ᶜⁿ = ⊥̂
(C ∧̂ D)     [ σ ]ᶜⁿ = C [ σ ]ᶜⁿ ∧̂ D [ σ ]ᶜⁿ
(A ≾̂ᵥᶜ B)   [ σ ]ᶜⁿ = A [ σ ]ᵛ ≾̂ᵥᶜ B [ σ ]ᵛ
(ρ ≾̂ᵣᶜ ρ')  [ σ ]ᶜⁿ = ρ [ σ ]ʳ ≾̂ᵣᶜ ρ' [ σ ]ʳ
(ε ≾̂ₑᶜ ε')  [ σ ]ᶜⁿ = ε [ σ ]ᵉ ≾̂ₑᶜ ε' [ σ ]ᵉ
Etᶜ A       [ σ ]ᶜⁿ = Etᶜ (A [ σ ]ᵛ)
Et∨≾ᵘ A ρ   [ σ ]ᶜⁿ = Et∨≾ᵘ (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
(∃ᵗ C)      [ σ ]ᶜⁿ = ∃ᵗ (C [ σ ↑ᵗ ]ᶜⁿ)
(∃ʳ C)      [ σ ]ᶜⁿ = ∃ʳ (C [ σ ↑ʳ ]ᶜⁿ)
(∃ᵉ C)      [ σ ]ᶜⁿ = ∃ᵉ (C [ σ ↑ᵉ ]ᶜⁿ)
(∀ᵉ C)      [ σ ]ᶜⁿ = ∀ᵉ (C [ σ ↑ᵉ ]ᶜⁿ)
⋀ᵒᵖ f       [ σ ]ᶜⁿ = ⋀ᵒᵖ (λ op → f op [ σ ]ᶜⁿ)

-- A constraint with no rigid binder

RigidFree : ∀ {Θ} → Constraint Θ → Set
RigidFree (C ∧̂ D) = RigidFree C × RigidFree D
RigidFree (∃ᵗ C)  = RigidFree C
RigidFree (∃ʳ C)  = RigidFree C
RigidFree (∃ᵉ C)  = RigidFree C
RigidFree (∀ᵉ C)  = ⊥
RigidFree (⋀ᵒᵖ f) = ∀ op → RigidFree (f op)
RigidFree _       = ⊤
