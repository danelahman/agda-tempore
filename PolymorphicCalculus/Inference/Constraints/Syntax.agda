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
-- Derived forms: conjunctions over a list, existential         --
-- quantification over the variables of a scope (`∃ˢ`), and     --
-- rigid quantification over several effect-grade variables     --
-- (`∀ᵉⁿ`).                                                     --
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
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.Constraints.Syntax (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses.Quantified S using (_+eⁿ_)

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

-- A conjunction over a list

⋀ᴸ : ∀ {Θ} {A : Set} → List A → (A → Constraint Θ) → Constraint Θ
⋀ᴸ []       f = ⊤̂
⋀ᴸ (x ∷ xs) f = f x ∧̂ ⋀ᴸ xs f

-- Existential quantification over fresh variables of one sort, the
-- innermost first, and over the variables of a scope

∃ᵗ* : ∀ {Θ} → (a : ℕ) → Constraint (scope (a + nTy Θ) (nR Θ) (nE Θ)) → Constraint Θ
∃ᵗ* zero        C = C
∃ᵗ* {Θ} (suc a) C = ∃ᵗ* a (∃ᵗ_ {Θ = scope (a + nTy Θ) (nR Θ) (nE Θ)} C)

∃ʳ* : ∀ {Θ} → (b : ℕ) → Constraint (scope (nTy Θ) (b + nR Θ) (nE Θ)) → Constraint Θ
∃ʳ* zero        C = C
∃ʳ* {Θ} (suc b) C = ∃ʳ* b (∃ʳ_ {Θ = scope (nTy Θ) (b + nR Θ) (nE Θ)} C)

∃ᵉ* : ∀ {Θ} → (c : ℕ) → Constraint (scope (nTy Θ) (nR Θ) (c + nE Θ)) → Constraint Θ
∃ᵉ* zero        C = C
∃ᵉ* {Θ} (suc c) C = ∃ᵉ* c (∃ᵉ_ {Θ = scope (nTy Θ) (nR Θ) (c + nE Θ)} C)

∃ˢ : ∀ {Θ} → (Ψ : Scope) → Constraint (Θ ⊹ Ψ) → Constraint Θ
∃ˢ {Θ} Ψ C =
  ∃ᵗ* (nTy Ψ)
    (∃ʳ* {Θ = scope (nTy Ψ + nTy Θ) (nR Θ) (nE Θ)} (nR Ψ)
      (∃ᵉ* {Θ = scope (nTy Ψ + nTy Θ) (nR Ψ + nR Θ) (nE Θ)} (nE Ψ) C))

-- Rigid quantification over several effect-grade variables, the
-- outermost first

∀ᵉⁿ : ∀ {Θ} → (k : ℕ) → Constraint (Θ +eⁿ k) → Constraint Θ
∀ᵉⁿ zero    C = C
∀ᵉⁿ (suc k) C = ∀ᵉ (∀ᵉⁿ k C)

-- Binders are traversed with the lifts `_↑ᵗ`/`_↑ʳ`/`_↑ᵉ` of
-- `PolymorphicCalculus.Syntax.GradeSubstitution`; weakening is a
-- substitution like any other.

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
