------------------------------------------------------------------
-- The invariants of a residual: I1′ on its orderings, I5 on its  --
-- deferred entries, and good grades in its subtyping demands     --
------------------------------------------------------------------

open import Data.List.Base using (map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.Product using (_×_; _,_)

open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Invariants.Residual (S : LanguageSpec) where

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S
open import TypeInference.OpenSyntax.Subst  S
open import TypeInference.OpenSyntax.Hyps   S using (mapᵖ)
open import TypeInference.OpenSyntax.Instances S using (_↑ᵉⁿ_)

open import TypeInference.SolverImpl.Deferred S
open import TypeInference.SolverImpl.Resid    S
open import TypeInference.SolverImpl.Localise S using (Outerₑ; Outerᵣ)
open import TypeInference.SolverImpl.Invariants.Outer S

------------------------------------------------------------------------
-- The invariants

-- The greater sides of an entry's orderings, over the unknowns free in
-- `P` and the entry's rigids

record Great {Θ Ψ} (P : Subst Θ Ψ) (E : Dfr Ψ) : Set where
  constructor mkGreat
  field
    greatʳ : ∀ {x y} → (x , y) ∈ ors (body E) → Outerᵣ (P ↑ᵉⁿ nb E) y
    greatᵉ : ∀ {x y} → (x , y) ∈ oes (body E) → Outerₑ (P ↑ᵉⁿ nb E) y

open Great public

record ResInv {Θ Ψ} (P : Subst Θ Ψ) (R : Resid Ψ) : Set where
  constructor mkResInv
  field
    inv-ss : ∀ {A B} → (A , B) ∈ ss R → TyGoodᵛ P A × TyGoodᵛ P B
    I1′ʳ   : ∀ {x y} → (x , y) ∈ rs R → Goodᵣ P y
    I1′ᵉ   : ∀ {x y} → (x , y) ∈ es R → Goodₑ P y
    I5     : ∀ {E} → E ∈ dfs R → Great P E

open ResInv public

------------------------------------------------------------------------
-- Entries

great-⊆ : ∀ {Θ Θ' Ψ} {P : Subst Θ Ψ} {P' : Subst Θ' Ψ} → P ⊆ᶠ P' → (E : Dfr Ψ)
        → Great P E → Great P' E
great-⊆ i E g =
  mkGreat (λ {x} {y} m → outerᵣ-⊆ {ρ = y} (⊆ᶠ-↑ᵉⁿ (nb E) i) (greatʳ g m))
          (λ {x} {y} m → outerₑ-⊆ {ε = y} (⊆ᶠ-↑ᵉⁿ (nb E) i) (greatᵉ g m))

great-⨟ : ∀ {Θ Ψ Ψ'} (P : Subst Θ Ψ) (σ : Subst Ψ Ψ') → (E : Dfr Ψ)
        → Great P E → Great (P ⨟ˢ σ) (E [ σ ]ᵈ)
great-⨟ P σ (dfr l k o) g = mkGreat r e
  where
    eq : ((P ↑ᵉⁿ k) ⨟ˢ (σ ↑ᵉⁿ k)) ⊆ᶠ ((P ⨟ˢ σ) ↑ᵉⁿ k)
    eq = ≐→⊆ᶠ (⨟-↑ᵉⁿ P σ k)

    r : ∀ {x y} → (x , y) ∈ ors (o [ σ ↑ᵉⁿ k ]ᴼ) → Outerᵣ ((P ⨟ˢ σ) ↑ᵉⁿ k) y
    r m with ∈-map⁻ (mapᵖ (_[ σ ↑ᵉⁿ k ]ʳ)) m
    ... | (x₀ , y₀) , m₀ , refl =
          outerᵣ-⊆ {ρ = y₀ [ σ ↑ᵉⁿ k ]ʳ} eq
                   (outerᵣ-⨟ (P ↑ᵉⁿ k) (σ ↑ᵉⁿ k) {y₀} (greatʳ g m₀))

    e : ∀ {x y} → (x , y) ∈ oes (o [ σ ↑ᵉⁿ k ]ᴼ) → Outerₑ ((P ⨟ˢ σ) ↑ᵉⁿ k) y
    e m with ∈-map⁻ (mapᵖ (_[ σ ↑ᵉⁿ k ]ᵉ)) m
    ... | (x₀ , y₀) , m₀ , refl =
          outerₑ-⊆ {ε = y₀ [ σ ↑ᵉⁿ k ]ᵉ} eq
                   (outerₑ-⨟ (P ↑ᵉⁿ k) (σ ↑ᵉⁿ k) {y₀} (greatᵉ g m₀))

