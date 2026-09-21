------------------------------------------------------------------
-- Satisfaction of constraints                                  --
--                                                              --
-- `σ ⊨[ Q ] C` reads: the substitution `σ` together with the   --
-- residual hypothesis set `Q` solves the constraint `C`. It is --
-- Set-valued and informative — the ∃-clauses carry their       --
-- witnesses, which elaboration reads back off.                 --
--                                                              --
-- `σ` need not ground anything: a pair `(σ , Q)` is a solution --
-- with residue: "residual constraint" in OutsideIn(X)'s sense  --
-- (Vytiniotis et al., JFP 2011), cf. Pretnar's types with      --
-- constraint sets (LMCS 2014).                                 --
--                                                              --
-- Constraint satisfaction follows Pottier and Remy (ATTAPL,    --
-- 2005); here it is proof-relevant, reading the binders as     --
-- Sigma and Pi.                                                --
------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Constraints.Satisfaction (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

open import TypeInference.Constraints.Syntax S

-- Satisfaction

infix 4 _⊨[_]_

_⊨[_]_ : ∀ {Θ Θ'} → Subst Θ Θ' → Hyps Θ' → Constraint Θ → Set
σ ⊨[ Q ] ⊤̂                       = ⊤
σ ⊨[ Q ] ⊥̂                       = ⊥
σ ⊨[ Q ] (C ∧̂ D)                 = σ ⊨[ Q ] C × σ ⊨[ Q ] D
σ ⊨[ Q ] (A ≐ᵥ B)                = A [ σ ]ᵛ ≡ B [ σ ]ᵛ
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

-- Sanity checks

private

  -- An existential over types is solved by any witness; the `∃`-clause's
  -- `Σ` and the extension `_,ᵗ_` compute as expected.

  ex-∃ᵗ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
        → σ ⊨[ Q ] (∃ᵗ (tvar (newᵗ {Θ}) ≐ᵥ tvar (newᵗ {Θ})))
  ex-∃ᵗ = Unit , refl

  -- A rigid effect-grade variable is its own witness under `_↑ᵉ`.

  ex-∀ᵉ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
        → σ ⊨[ Q ] (∀ᵉ (evar (newᵉ {Θ}) ≾̂ₑᶜ evar (newᵉ {Θ})))
  ex-∀ᵉ = ⊩≾̂ₑ-refl

  -- The two components of a conjunction are read off independently.

  ex-∧̂ : ∀ {Θ Θ'} {σ : Subst Θ Θ'} {Q : Hyps Θ'}
       → σ ⊨[ Q ] (⊤̂ ∧̂ (∃ʳ (rvar (newʳ {Θ}) ≾̂ᵣᶜ rvar (newʳ {Θ}))))
  ex-∧̂ = tt , (ûᵣ , ⊩≾̂ᵣ-refl)
