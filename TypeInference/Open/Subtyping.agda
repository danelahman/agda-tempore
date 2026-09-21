-------------------------------------------------------------------
-- Consequences of open subtyping                                  --
--                                                                 --
-- Inversion at a type former and stability under the scope        --
-- extensions.                                                     --
--                                                                 --
-- The relation `_∣_<:̂ᵛ_` itself, together with reflexivity,        --
-- transitivity, eternality transfer and stability under a scope    --
-- substitution, is defined with the hypothesis sets: `_⊩ᴴ_[_]`     --
-- states what an assumed subtyping transports to, so it mentions   --
-- the relation.                                                    --
-------------------------------------------------------------------

open import Data.Product using (Σ-syntax; _×_; _,_)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Open.Subtyping (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S
open import TypeInference.Open.Hyps   S

-- Inversion at the formers with no proper supertype

<:̂ᵛ-Baseˡ : ∀ {Θ} {Q : Hyps Θ} {b A} → Q ∣ Base b <:̂ᵛ A → A ≡ Base b
<:̂ᵛ-Baseˡ (Baseₛ refl) = refl

<:̂ᵛ-Unitˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Unit <:̂ᵛ A → A ≡ Unit
<:̂ᵛ-Unitˡ Unitₛ = refl

<:̂ᵛ-Boolˡ : ∀ {Θ} {Q : Hyps Θ} {A} → Q ∣ Bool <:̂ᵛ A → A ≡ Bool
<:̂ᵛ-Boolˡ Boolₛ = refl

-- Inversion at a product: a supertype is a product, componentwise

<:̂ᵛ-×ˡ : ∀ {Θ} {Q : Hyps Θ} {A₁ A₂ B}
       → Q ∣ A₁ |×| A₂ <:̂ᵛ B
       → Σ[ B₁ ∈ OVType Θ ] Σ[ B₂ ∈ OVType Θ ]
           (B ≡ B₁ |×| B₂) × (Q ∣ A₁ <:̂ᵛ B₁) × (Q ∣ A₂ <:̂ᵛ B₂)
<:̂ᵛ-×ˡ (p |×|ₛ q) = _ , _ , refl , p , q

-- Inversion at box type

<:̂ᵛ-box-grade : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
              → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ⊩ ρ' ≾̂ᵣ ρ
<:̂ᵛ-box-grade ([ q ]ₛ _) = q

<:̂ᵛ-box-type : ∀ {Θ} {Q : Hyps Θ} {ρ ρ' A A'}
             → Q ∣ ([ ρ ] A) <:̂ᵛ ([ ρ' ] A') → Q ∣ A <:̂ᵛ A'
<:̂ᵛ-box-type ([ _ ]ₛ p) = p

-- Stability under the scope extensions

<:̂ᵛ-wkᵗ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵗ-H Q ∣ wkᵗ-v A <:̂ᵛ wkᵗ-v A'
<:̂ᵛ-wkᵗ {Q = Q} {A} {A'} p =
  subst₂ (wkᵗ-H Q ∣_<:̂ᵛ_) (wkˢᵗ-v A) (wkˢᵗ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵗ p)

<:̂ᵛ-wkʳ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkʳ-H Q ∣ wkʳ-v A <:̂ᵛ wkʳ-v A'
<:̂ᵛ-wkʳ {Q = Q} {A} {A'} p =
  subst₂ (wkʳ-H Q ∣_<:̂ᵛ_) (wkˢʳ-v A) (wkˢʳ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkʳ p)

<:̂ᵛ-wkᵉ : ∀ {Θ} {Q : Hyps Θ} {A A'}
        → Q ∣ A <:̂ᵛ A' → wkᵉ-H Q ∣ wkᵉ-v A <:̂ᵛ wkᵉ-v A'
<:̂ᵛ-wkᵉ {Q = Q} {A} {A'} p =
  subst₂ (wkᵉ-H Q ∣_<:̂ᵛ_) (wkˢᵉ-v A) (wkˢᵉ-v A') (<:̂ᵛ-subst ⊩ᴴ-wkᵉ p)
