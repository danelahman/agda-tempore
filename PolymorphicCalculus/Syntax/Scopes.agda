------------------------------------------------------------------
-- Scopes of type, resource-grade and effect-grade variables    --
--                                                              --
-- The polymorphic calculus is indexed by a `Scope`, a record   --
-- of three counters, one for each sort of variable. Every      --
-- scope extension reduces definitionally.                      --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)

module PolymorphicCalculus.Syntax.Scopes where

record Scope : Set where
  constructor scope
  field
    nTy : ℕ                        -- number of type variables
    nR  : ℕ                        -- number of resource-grade variables
    nE  : ℕ                        -- number of effect-grade variables

open Scope public

-- Variables of the three sorts

TyVar : Scope → Set
TyVar Θ = Fin (nTy Θ)

RVar : Scope → Set
RVar Θ = Fin (nR Θ)

EVar : Scope → Set
EVar Θ = Fin (nE Θ)

∅ˢ : Scope
∅ˢ = scope 0 0 0

-- Scope extensions, each incrementing one counter

_+ty : Scope → Scope
Θ +ty = scope (suc (nTy Θ)) (nR Θ) (nE Θ)

_+r : Scope → Scope
Θ +r = scope (nTy Θ) (suc (nR Θ)) (nE Θ)

_+e : Scope → Scope
Θ +e = scope (nTy Θ) (nR Θ) (suc (nE Θ))

infixl 30 _+ty _+r _+e

-- The newly bound variable

newᵗ : ∀ {Θ} → TyVar (Θ +ty)
newᵗ = zero

newʳ : ∀ {Θ} → RVar (Θ +r)
newʳ = zero

newᵉ : ∀ {Θ} → EVar (Θ +e)
newᵉ = zero

-- Injections into an extension, `wk<extension>-<variable sort>`; the scope
-- is explicit, as `Fin` of a projection does not determine it

wkᵗ-tv : (Θ : Scope) → TyVar Θ → TyVar (Θ +ty)
wkᵗ-tv Θ i = suc i

wkᵗ-rv : (Θ : Scope) → RVar Θ → RVar (Θ +ty)
wkᵗ-rv Θ i = i

wkᵗ-ev : (Θ : Scope) → EVar Θ → EVar (Θ +ty)
wkᵗ-ev Θ i = i

wkʳ-tv : (Θ : Scope) → TyVar Θ → TyVar (Θ +r)
wkʳ-tv Θ i = i

wkʳ-rv : (Θ : Scope) → RVar Θ → RVar (Θ +r)
wkʳ-rv Θ i = suc i

wkʳ-ev : (Θ : Scope) → EVar Θ → EVar (Θ +r)
wkʳ-ev Θ i = i

wkᵉ-tv : (Θ : Scope) → TyVar Θ → TyVar (Θ +e)
wkᵉ-tv Θ i = i

wkᵉ-rv : (Θ : Scope) → RVar Θ → RVar (Θ +e)
wkᵉ-rv Θ i = i

wkᵉ-ev : (Θ : Scope) → EVar Θ → EVar (Θ +e)
wkᵉ-ev Θ i = suc i
