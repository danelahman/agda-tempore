------------------------------------------------------------------
-- Obligations                                                  --
--                                                              --
-- An obligation `∀ᵉ j₁ … jₖ. O` is a list `O` of grade         --
-- orderings over the scope extended by `k` rigid effect-grade  --
-- variables, `j₁` outermost, labelled with the operation whose --
-- handler clause left it (for reading only). Substitution acts --
-- on an obligation under its rigids.                           --
------------------------------------------------------------------

open import Data.List.Base using (List; map)
open import Data.Maybe.Base using (Maybe)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.OpenSyntax.Obligations (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops using (Op)

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Subst  S

------------------------------------------------------------------------
-- Rigid binders

infixl 30 _+eⁿ_ _↑ᵉⁿ_

-- The rigids are bound outermost first: the scope extended by `k + 1`
-- rigids is the scope extended by one, then by `k`.

_+eⁿ_ : Scope → ℕ → Scope
Θ +eⁿ zero  = Θ
Θ +eⁿ suc k = (Θ +e) +eⁿ k

_↑ᵉⁿ_ : ∀ {Θ Θ'} → Subst Θ Θ' → (k : ℕ) → Subst (Θ +eⁿ k) (Θ' +eⁿ k)
σ ↑ᵉⁿ zero  = σ
σ ↑ᵉⁿ suc k = (σ ↑ᵉ) ↑ᵉⁿ k

≐ˢ-↑ᵉⁿ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (k : ℕ) → (σ ↑ᵉⁿ k) ≐ˢ (σ' ↑ᵉⁿ k)
≐ˢ-↑ᵉⁿ p zero    = p
≐ˢ-↑ᵉⁿ p (suc k) = ≐ˢ-↑ᵉⁿ (≐ˢ-↑ᵉ p) k

⨟-↑ᵉⁿ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (δ : Subst Θ₁ Θ₂) → (k : ℕ)
      → ((σ ↑ᵉⁿ k) ⨟ˢ (δ ↑ᵉⁿ k)) ≐ˢ ((σ ⨟ˢ δ) ↑ᵉⁿ k)
⨟-↑ᵉⁿ σ δ zero    = ≐ˢ-refl
⨟-↑ᵉⁿ σ δ (suc k) = ≐ˢ-trans (⨟-↑ᵉⁿ (σ ↑ᵉ) (δ ↑ᵉ) k) (≐ˢ-↑ᵉⁿ (⨟-↑ᵉ σ δ) k)

------------------------------------------------------------------------
-- Grade orderings

-- Pairwise action of a function on a homogeneous pair

mapᵖ : ∀ {A B : Set} → (A → B) → A × A → B × B
mapᵖ f (x , y) = f x , f y

record Ords (Ψ : Scope) : Set where
  constructor ords
  field
    ors : List (RExp Ψ × RExp Ψ)
    oes : List (EExp Ψ × EExp Ψ)

open Ords public

infixl 50 _[_]ᴼ

_[_]ᴼ : ∀ {Ψ Ψ'} → Ords Ψ → Subst Ψ Ψ' → Ords Ψ'
o [ σ ]ᴼ = ords (map (mapᵖ (_[ σ ]ʳ)) (ors o)) (map (mapᵖ (_[ σ ]ᵉ)) (oes o))

------------------------------------------------------------------------
-- Obligations

record Oblig (Θ : Scope) : Set where
  constructor oblig
  field
    label  : Maybe Op
    rigids : ℕ
    body   : Ords (Θ +eⁿ rigids)

open Oblig public

Obligs : Scope → Set
Obligs Θ = List (Oblig Θ)

infixl 50 _[_]ᵒᵇ

_[_]ᵒᵇ : ∀ {Θ Θ'} → Oblig Θ → Subst Θ Θ' → Oblig Θ'
oblig l k o [ σ ]ᵒᵇ = oblig l k (o [ σ ↑ᵉⁿ k ]ᴼ)
