------------------------------------------------------------------
-- Lookup and membership under weakening and substitution       --
--                                                              --
-- Lookup and membership commute with the three scope           --
-- extensions; a substitution or a type equation acts on        --
-- membership witnesses, keeping the position.                  --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Syntax.Contexts.Properties (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.Contexts          S
open import PolymorphicCalculus.Syntax.GradeSubstitution S

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

∈̂-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
           → A ≡ A' → A ∈̂[ ρ ] Γ → A' ∈̂[ ρ ] Γ
∈̂-ty-subst refl x = x

var-pos-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                 → (e : A ≡ A') → (x : A ∈̂[ ρ ] Γ)
                 → var-pos (∈̂-ty-subst e x) ≡ var-pos x
var-pos-ty-subst refl x = refl
