------------------------------------------------------------------
-- Lookup and membership under weakening and substitution         --
--                                                                --
-- The commutation facts the `var` and `unbox` cases of the       --
-- inference proofs need. Generation looks a variable up in a     --
-- *weakened* context (`lookup-ty Γ↑ i`), while the mirrored      --
-- rules take their membership witness in a *substituted* one;    --
-- the two are related by the lemmas below.                       --
--                                                                --
-- `Inference.Open.Contexts` and `Inference.Open.Subst` already   --
-- carry the corresponding facts for substitution; this module    --
-- adds the ones for the three scope extensions and the actions   --
-- of a substitution and of a type equation on membership         --
-- witnesses.                                                     --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.Open.ContextsLemmas (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Inference.Open.Grades   S
open import Inference.Open.Types    S
open import Inference.Open.Contexts S
open import Inference.Open.Subst    S

--------------------------------------------------------------
-- Lookup commutes with the three scope extensions           --
--                                                           --
-- Each is the induction that mirrors `lookup-*`'s own        --
-- recursion; the `[]` case is covered by `Fin 0` being empty. --
--------------------------------------------------------------

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

--------------------------------------------------------------
-- Action of a substitution on a membership witness          --
--                                                           --
-- Index-preserving, as `_[_]ᶜᵗˣ` is: the witness is rebuilt  --
-- constructor for constructor, so its position is untouched. --
--------------------------------------------------------------

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

--------------------------------------------------------------
-- Transporting a membership witness along a type equation   --
--                                                           --
-- The `unbox` rule wants the looked-up type in the shape     --
-- `[ ρ ] A`; the equation that puts it there comes from the  --
-- `_≐ᵥ_` conjunct. Transporting is `J`, so the position      --
-- cannot change.                                             --
--------------------------------------------------------------

∈̂-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
           → A ≡ A' → A ∈̂[ ρ ] Γ → A' ∈̂[ ρ ] Γ
∈̂-ty-subst refl x = x

var-pos-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                 → (e : A ≡ A') → (x : A ∈̂[ ρ ] Γ)
                 → var-pos (∈̂-ty-subst e x) ≡ var-pos x
var-pos-ty-subst refl x = refl
