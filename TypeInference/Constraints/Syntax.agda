------------------------------------------------------------------
-- The constraint language                                       --
--                                                               --
-- Constraints are the output of type-and-effect inference: a    --
-- first-order formula over the open types and grade expressions --
-- of a scope `Θ`, built from type equations, value-type         --
-- subtyping, grade orderings, eternality atoms, existential     --
-- quantification over the three sorts of variables, a rigid     --
-- (eigenvariable) effect-grade quantifier, and a conjunction    --
-- indexed by operation symbols.                                 --
--                                                               --
-- Computation types need no former of their own: `C ≾̂ᶜ C'` is   --
-- `(A ≾̂ᵥᶜ A') ∧̂ (ε ≾̂ₑᶜ ε')`.                                    --
--                                                               --
-- Constraints with binders follow Pottier and Remy, The Essence --
-- of ML Type Inference (ATTAPL, 2005).                          --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

module TypeInference.Constraints.Syntax (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S

-- Constraints

data Constraint (Θ : Scope) : Set where
  ⊤̂     : Constraint Θ                                -- trivially satisfied
  ⊥̂     : Constraint Θ                                -- unsatisfiable
  _∧̂_   : Constraint Θ → Constraint Θ → Constraint Θ  -- conjunction
  _≐ᵥ_  : OVType Θ → OVType Θ → Constraint Θ          -- type equation
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

infixr 6 _∧̂_
infix  4 _≐ᵥ_ _≾̂ᵥᶜ_ _≾̂ᵣᶜ_ _≾̂ₑᶜ_
infix  2 ∃ᵗ_ ∃ʳ_ ∃ᵉ_ ∀ᵉ_

-- Binders are traversed with the lifts `_↑ᵗ`/`_↑ʳ`/`_↑ᵉ` of
-- `TypeInference.Open.Subst`; weakening is a substitution like any other.

infixl 50 _[_]ᶜⁿ

_[_]ᶜⁿ : ∀ {Θ Θ'} → Constraint Θ → Subst Θ Θ' → Constraint Θ'
⊤̂           [ σ ]ᶜⁿ = ⊤̂
⊥̂           [ σ ]ᶜⁿ = ⊥̂
(C ∧̂ D)     [ σ ]ᶜⁿ = C [ σ ]ᶜⁿ ∧̂ D [ σ ]ᶜⁿ
(A ≐ᵥ B)    [ σ ]ᶜⁿ = A [ σ ]ᵛ ≐ᵥ B [ σ ]ᵛ
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
