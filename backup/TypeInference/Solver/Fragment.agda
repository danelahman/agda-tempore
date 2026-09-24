------------------------------------------------------------------
-- The rigid-binder-free fragment                                --
--                                                                --
-- `NoRig` restricts refutation only: a failed discharge at a     --
-- rigid binder is a decision-procedure failure, not a proof of   --
-- unsatisfiability.                                              --
------------------------------------------------------------------

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

module TypeInference.Solver.Fragment (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

open import TypeInference.Constraints.Syntax S

data NoRig {Θ : Scope} : Constraint Θ → Set where
  ⊤ⁿ    : NoRig ⊤̂
  ⊥ⁿ    : NoRig ⊥̂
  _∧ⁿ_  : ∀ {C D} → NoRig C → NoRig D → NoRig (C ∧̂ D)
  ≐ⁿ    : ∀ {A B} → NoRig (A ≐ᵥ B)
  ≾ᵥⁿ   : ∀ {A B} → NoRig (A ≾̂ᵥᶜ B)
  ≾ᵣⁿ   : ∀ {ρ ρ'} → NoRig (ρ ≾̂ᵣᶜ ρ')
  ≾ₑⁿ   : ∀ {ε ε'} → NoRig (ε ≾̂ₑᶜ ε')
  Etⁿ   : ∀ {A} → NoRig (Etᶜ A)
  Et∨ⁿ  : ∀ {A ρ} → NoRig (Et∨≾ᵘ A ρ)
  ∃ᵗⁿ   : ∀ {C} → NoRig C → NoRig (∃ᵗ C)
  ∃ʳⁿ   : ∀ {C} → NoRig C → NoRig (∃ʳ C)
  ∃ᵉⁿ   : ∀ {C} → NoRig C → NoRig (∃ᵉ C)
  ⋀ⁿ    : ∀ {f} → ((op : Op) → NoRig (f op)) → NoRig (⋀ᵒᵖ f)

infixr 6 _∧ⁿ_
