------------------------------------------------------------------
-- The rigid-binder-free fragment                                --
--                                                                --
-- `NoRig` restricts refutation only: a failed discharge at a     --
-- rigid binder is a decision-procedure failure, not a proof of   --
-- unsatisfiability.                                              --
------------------------------------------------------------------

open import Data.Maybe.Base using (Maybe; just; nothing)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Enum using (OpEnum)

module TypeInference.Solver.Fragment (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

open import TypeInference.Constraints.Syntax S

open import TypeInference.SolverImpl.Enum S using (AllOp; all-lookup; all-build)

data NoRig {Θ : Scope} : Constraint Θ → Set where
  ⊤ⁿ    : NoRig ⊤̂
  ⊥ⁿ    : NoRig ⊥̂
  _∧ⁿ_  : ∀ {C D} → NoRig C → NoRig D → NoRig (C ∧̂ D)
  ≐ⁿ    : ∀ {A B} → NoRig (A ≐ᵥ B)
  ≾ᵣⁿ   : ∀ {ρ ρ'} → NoRig (ρ ≾̂ᵣᶜ ρ')
  ≾ₑⁿ   : ∀ {ε ε'} → NoRig (ε ≾̂ₑᶜ ε')
  Etⁿ   : ∀ {A} → NoRig (Etᶜ A)
  Et∨ⁿ  : ∀ {A ρ} → NoRig (Et∨≾ᵘ A ρ)
  ∃ᵗⁿ   : ∀ {C} → NoRig C → NoRig (∃ᵗ C)
  ∃ʳⁿ   : ∀ {C} → NoRig C → NoRig (∃ʳ C)
  ∃ᵉⁿ   : ∀ {C} → NoRig C → NoRig (∃ᵉ C)
  ⋀ⁿ    : ∀ {f} → ((op : Op) → NoRig (f op)) → NoRig (⋀ᵒᵖ f)

infixr 6 _∧ⁿ_

-- `⋀ᵒᵖ` carries a function, so its clause is decided by exhausting an
-- enumeration of the operation symbols and reading the result back
-- with `all-lookup`.

norig? : ∀ {Θ} → OpEnum S → (C : Constraint Θ) → Maybe (NoRig C)
norig? oe ⊤̂            = just ⊤ⁿ
norig? oe ⊥̂            = just ⊥ⁿ
norig? oe (C ∧̂ D) with norig? oe C | norig? oe D
... | just p  | just q  = just (p ∧ⁿ q)
... | _       | _       = nothing
norig? oe (A ≐ᵥ B)     = just ≐ⁿ
norig? oe (ρ ≾̂ᵣᶜ ρ')   = just ≾ᵣⁿ
norig? oe (ε ≾̂ₑᶜ ε')   = just ≾ₑⁿ
norig? oe (Etᶜ A)      = just Etⁿ
norig? oe (Et∨≾ᵘ A ρ)  = just Et∨ⁿ
norig? oe (∃ᵗ C) with norig? oe C
... | just p  = just (∃ᵗⁿ p)
... | nothing = nothing
norig? oe (∃ʳ C) with norig? oe C
... | just p  = just (∃ʳⁿ p)
... | nothing = nothing
norig? oe (∃ᵉ C) with norig? oe C
... | just p  = just (∃ᵉⁿ p)
... | nothing = nothing
norig? oe (∀ᵉ C)       = nothing
norig? oe (⋀ᵒᵖ f) with all-build (λ op → norig? oe (f op)) (OpEnum.ops oe)
... | just ps = just (⋀ⁿ (λ op → all-lookup ps (OpEnum.complete oe op)))
... | nothing = nothing
