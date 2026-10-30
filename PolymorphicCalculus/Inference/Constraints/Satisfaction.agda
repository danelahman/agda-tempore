------------------------------------------------------------------
-- Satisfaction of constraints                                  --
--                                                              --
-- `σ ⊨[ Q ] C` states that the substitution `σ`, together with --
-- the residual hypothesis set `Q`, solves the constraint `C`.  --
-- It is proof-relevant: the ∃-clauses carry their witnesses,   --
-- from which elaboration reads a derivation. `σ` need not be   --
-- ground, so a pair `(σ , Q)` is a solution with residual      --
-- constraints.                                                 --
--                                                              --
-- `σ ⊨[ Q ∣ R ] C` states that `σ` solves `C` relative to `Q`  --
-- and further quantified orderings `R`: along every            --
-- substitution `δ`, under any hypotheses entailing `Q` and `R` --
-- along `δ`, `σ ⨟ δ` solves `C`.                               --
--                                                              --
-- Constraint satisfaction follows Pottier and Rémy, The        --
-- Essence of ML Type Inference (ATTAPL, 2005), here            --
-- proof-relevant; "residual constraint" is the term of         --
-- OutsideIn(X) (Vytiniotis et al., JFP 2011); cf. Pretnar,     --
-- Inferring Algebraic Effects (LMCS 2014).                     --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.Constraints.Satisfaction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import PolymorphicCalculus.Syntax.Grades S
open import PolymorphicCalculus.Syntax.Types  S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses   S
open import PolymorphicCalculus.Hypotheses.Instances S using (_⊩_∣_[_])

open import PolymorphicCalculus.Inference.Constraints.Syntax S

-- Satisfaction

infix 4 _⊨[_]_

_⊨[_]_ : ∀ {Θ Θ'} → Subst Θ Θ' → Hyps Θ' → Constraint Θ → Set
σ ⊨[ Q ] ⊤̂                       = ⊤
σ ⊨[ Q ] ⊥̂                       = ⊥
σ ⊨[ Q ] (C ∧̂ D)                 = σ ⊨[ Q ] C × σ ⊨[ Q ] D
σ ⊨[ Q ] (A ≾̂ᵥᶜ B)               = Q ∣ A [ σ ]ᵛ <:̂ᵛ B [ σ ]ᵛ
σ ⊨[ Q ] (ρ ≾̂ᵣᶜ ρ')              = Q ⊩ ρ [ σ ]ʳ ≾̂ᵣ ρ' [ σ ]ʳ
σ ⊨[ Q ] (ε ≾̂ₑᶜ ε')              = Q ⊩ ε [ σ ]ᵉ ≾̂ₑ ε' [ σ ]ᵉ
σ ⊨[ Q ] Etᶜ A                   = Q ⊩ᴱ A [ σ ]ᵛ
σ ⊨[ Q ] Et∨≾ᵘ A ρ               = VarOK Q (A [ σ ]ᵛ) (ρ [ σ ]ʳ)
_⊨[_]_ {Θ' = Θ'} σ Q (∃ᵗ C)      = Σ[ B ∈ OVType Θ' ] ((σ ,ᵗ B) ⊨[ Q ] C)
_⊨[_]_ {Θ' = Θ'} σ Q (∃ʳ C)      = Σ[ ρ ∈ RExp Θ' ]   ((σ ,ʳ ρ) ⊨[ Q ] C)
_⊨[_]_ {Θ' = Θ'} σ Q (∃ᵉ C)      = Σ[ ε ∈ EExp Θ' ]   ((σ ,ᵉ ε) ⊨[ Q ] C)
σ ⊨[ Q ] (∀ᵉ C)                  = (σ ↑ᵉ) ⊨[ wkᵉ-H Q ] C
σ ⊨[ Q ] ⋀ᵒᵖ f                   = (op : Op) → σ ⊨[ Q ] f op

-- Relative to hypotheses and further quantified orderings

infix 4 _⊨[_∣_]_

_⊨[_∣_]_ : ∀ {Θ Θ'} → Subst Θ Θ' → Hyps Θ' → QOrds Θ' → Constraint Θ → Set
_⊨[_∣_]_ {Θ' = Θ'} σ Q R C =
  ∀ {Ξ} → (δ : Subst Θ' Ξ) → (Q' : Hyps Ξ) → Q' ⊩ Q ∣ R [ δ ] → (σ ⨟ˢ δ) ⊨[ Q' ] C

-- Sanity checks: the binder clauses compute.

private

  -- An existential over types is solved by any witness; the `∃`-clause's
  -- `Σ` and the extension `_,ᵗ_` compute as expected, and a type
  -- equation is read as subtyping both ways.

  ex-∃ᵗ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
        → σ ⊨[ Q ] (∃ᵗ (tvar (newᵗ {Θ}) ≐ᵥ tvar (newᵗ {Θ})))
  ex-∃ᵗ = Unit , Unitₛ , Unitₛ

  -- A rigid effect-grade variable is its own witness under `_↑ᵉ`.

  ex-∀ᵉ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
        → σ ⊨[ Q ] (∀ᵉ (evar (newᵉ {Θ}) ≾̂ₑᶜ evar (newᵉ {Θ})))
  ex-∀ᵉ = ⊩≾̂ₑ-refl

  -- The two components of a conjunction are read off independently.

  ex-∧̂ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
       → σ ⊨[ Q ] (⊤̂ ∧̂ (∃ʳ (rvar (newʳ {Θ}) ≾̂ᵣᶜ rvar (newʳ {Θ}))))
  ex-∧̂ = tt , (ûᵣ , ⊩≾̂ᵣ-refl)
