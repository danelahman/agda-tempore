------------------------------------------------------------------
-- Lookup and membership under weakening and substitution       --
--                                                              --
-- Commutation of lookup and membership with the three scope    --
-- extensions, and the actions of a substitution and of a type  --
-- equation on membership witnesses, as used by the `var` and   --
-- `unbox` cases of the soundness and completeness proofs.      --
-- Generation looks a variable up in a weakened context; the    --
-- open rules take their membership witness in a substituted    --
-- one.                                                         --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Syntax.ContextsLemmas (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S
open import OpenCalculus.Syntax.Contexts S
open import OpenCalculus.Syntax.Subst    S

-- Lookup commutes with the three scope extensions.

lookup-ty-wkᵗ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-ty (wkᵗ-ctx Γ) i ≡ wkᵗ-v (lookup-ty Γ i)
lookup-ty-wkᵗ (Γ ∷ A)   zero    = refl
lookup-ty-wkᵗ (Γ ∷ A)   (suc i) = lookup-ty-wkᵗ Γ i
lookup-ty-wkᵗ (Γ ⟨ ρ ⟩) i       = lookup-ty-wkᵗ Γ i

lookup-ty-wkʳ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-ty (wkʳ-ctx Γ) i ≡ wkʳ-v (lookup-ty Γ i)
lookup-ty-wkʳ (Γ ∷ A)   zero    = refl
lookup-ty-wkʳ (Γ ∷ A)   (suc i) = lookup-ty-wkʳ Γ i
lookup-ty-wkʳ (Γ ⟨ ρ ⟩) i       = lookup-ty-wkʳ Γ i

lookup-ty-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-ty (wkᵉ-ctx Γ) i ≡ wkᵉ-v (lookup-ty Γ i)
lookup-ty-wkᵉ (Γ ∷ A)   zero    = refl
lookup-ty-wkᵉ (Γ ∷ A)   (suc i) = lookup-ty-wkᵉ Γ i
lookup-ty-wkᵉ (Γ ⟨ ρ ⟩) i       = lookup-ty-wkᵉ Γ i

lookup-gr-wkᵗ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-gr (wkᵗ-ctx Γ) i ≡ wkᵗ-r (lookup-gr Γ i)
lookup-gr-wkᵗ (Γ ∷ A)   zero    = refl
lookup-gr-wkᵗ (Γ ∷ A)   (suc i) = lookup-gr-wkᵗ Γ i
lookup-gr-wkᵗ (Γ ⟨ ρ ⟩) i       = cong (_·̂ᵣ wkᵗ-r ρ) (lookup-gr-wkᵗ Γ i)

lookup-gr-wkʳ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-gr (wkʳ-ctx Γ) i ≡ wkʳ-r (lookup-gr Γ i)
lookup-gr-wkʳ (Γ ∷ A)   zero    = refl
lookup-gr-wkʳ (Γ ∷ A)   (suc i) = lookup-gr-wkʳ Γ i
lookup-gr-wkʳ (Γ ⟨ ρ ⟩) i       = cong (_·̂ᵣ wkʳ-r ρ) (lookup-gr-wkʳ Γ i)

lookup-gr-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-gr (wkᵉ-ctx Γ) i ≡ wkᵉ-r (lookup-gr Γ i)
lookup-gr-wkᵉ (Γ ∷ A)   zero    = refl
lookup-gr-wkᵉ (Γ ∷ A)   (suc i) = lookup-gr-wkᵉ Γ i
lookup-gr-wkᵉ (Γ ⟨ ρ ⟩) i       = cong (_·̂ᵣ wkᵉ-r ρ) (lookup-gr-wkᵉ Γ i)

-- Substitution on a membership witness is index-preserving, as `_[_]ᶜᵗˣ`
-- is.

∈̂-subst : ∀ {Θ Θ' n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
        → (σ : Subst Θ Θ')
        → A ∈̂[ ρ ] Γ
        --------------------------------------------
        → (A [ σ ]ᵛ) ∈̂[ ρ [ σ ]ʳ ] (Γ [ σ ]ᶜᵗˣ)
∈̂-subst σ Hd        = Hd
∈̂-subst σ (Tl-∷ x)  = Tl-∷ (∈̂-subst σ x)
∈̂-subst σ (Tl-⟨⟩ x) = Tl-⟨⟩ (∈̂-subst σ x)

var-pos-∈̂-subst : ∀ {Θ Θ' n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                → (σ : Subst Θ Θ') → (x : A ∈̂[ ρ ] Γ)
                → var-pos (∈̂-subst σ x) ≡ var-pos x
var-pos-∈̂-subst σ Hd        = refl
var-pos-∈̂-subst σ (Tl-∷ x)  = cong suc (var-pos-∈̂-subst σ x)
var-pos-∈̂-subst σ (Tl-⟨⟩ x) = var-pos-∈̂-subst σ x

-- Transporting a membership witness along a type equation is `J`, so
-- the position cannot change.

∈̂-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
           → A ≡ A' → A ∈̂[ ρ ] Γ → A' ∈̂[ ρ ] Γ
∈̂-ty-subst refl x = x

var-pos-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                 → (e : A ≡ A') → (x : A ∈̂[ ρ ] Γ)
                 → var-pos (∈̂-ty-subst e x) ≡ var-pos x
var-pos-ty-subst refl x = refl
