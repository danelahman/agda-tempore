--------------------------------------------------------------------------------
-- Completeness checks at deadlines: `Kept` and `et-h`, as a constraint.      --
--                                                                            --
-- A var-rule disjunction at `Bool` whose lock is an effect unknown bounded   --
-- below by a clause's rigid, as the lock `∣ ε ∣` left by a resumption        --
-- `k · a` is. It holds by eternality, and is solved.                         --
--------------------------------------------------------------------------------

open import Data.Maybe using (just)
open import Data.Fin using (zero; suc)
open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Util.Equality

open import TypeInference.Scopes

open import TypeInference.SolverImpl.Demo.TimeIntervals using (specᵈ; module Gᵐ)

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Constraints where

open import TypeInference.OpenSyntax.Grades   specᵈ
open import TypeInference.OpenSyntax.Types    specᵈ
open import TypeInference.OpenSyntax.Hyps     specᵈ
open import TypeInference.OpenSyntax.Subst    specᵈ using (idˢ)
open import TypeInference.Constraints.Syntax  specᵈ using (Constraint; ∀ᵉ_; ∃ᵉ_; _∧̂_; _≾̂ₑᶜ_; Et∨≾ᵘ)
open import TypeInference.Constraints.Satisfaction specᵈ using (_⊨[_]_)

keptC : Constraint ∅ˢ
keptC = ∀ᵉ (∃ᵉ ((evar (suc zero) ≾̂ₑᶜ evar zero) ∧̂ Et∨≾ᵘ Bool (∣ evar zero ∣̂ᵉ)))

keptC-sat : idˢ ⊨[ ∅ᴴ ] keptC
keptC-sat = evar zero , ⊩≾̂ₑ-refl , et-ok Boolₑ

keptC-solved : Gᵐ.solved? (Gᵐ.gsolveImpl keptC) ≡ just tt
keptC-solved = refl
