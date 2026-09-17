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
-- adds the ones for the three scope extensions, the crossing     --
-- flag of a looked-up variable, and the actions of a             --
-- substitution and of a type equation on membership witnesses.   --
------------------------------------------------------------------

-- `Bool` is renamed, as `OVType` has a constructor of that name
open import Data.Bool using () renaming (Bool to 𝔹)
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
lookup-ty-wkᵗ (Γ ᴱ̂)     i       = lookup-ty-wkᵗ Γ i

lookup-ty-wkʳ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-ty (wkʳ-ctx Γ) i ≡ wkʳ-v (lookup-ty Γ i)
lookup-ty-wkʳ (Γ ∷ A)   zero    = refl
lookup-ty-wkʳ (Γ ∷ A)   (suc i) = lookup-ty-wkʳ Γ i
lookup-ty-wkʳ (Γ ⟨ ρ ⟩) i       = lookup-ty-wkʳ Γ i
lookup-ty-wkʳ (Γ ᴱ̂)     i       = lookup-ty-wkʳ Γ i

lookup-ty-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-ty (wkᵉ-ctx Γ) i ≡ wkᵉ-v (lookup-ty Γ i)
lookup-ty-wkᵉ (Γ ∷ A)   zero    = refl
lookup-ty-wkᵉ (Γ ∷ A)   (suc i) = lookup-ty-wkᵉ Γ i
lookup-ty-wkᵉ (Γ ⟨ ρ ⟩) i       = lookup-ty-wkᵉ Γ i
lookup-ty-wkᵉ (Γ ᴱ̂)     i       = lookup-ty-wkᵉ Γ i

lookup-gr-wkᵗ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-gr (wkᵗ-ctx Γ) i ≡ wkᵗ-r (lookup-gr Γ i)
lookup-gr-wkᵗ (Γ ∷ A)   zero    = refl
lookup-gr-wkᵗ (Γ ∷ A)   (suc i) = lookup-gr-wkᵗ Γ i
lookup-gr-wkᵗ (Γ ⟨ ρ ⟩) i       = cong (_·̂ᵣ wkᵗ-r ρ) (lookup-gr-wkᵗ Γ i)
lookup-gr-wkᵗ (Γ ᴱ̂)     i       = refl

lookup-gr-wkʳ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-gr (wkʳ-ctx Γ) i ≡ wkʳ-r (lookup-gr Γ i)
lookup-gr-wkʳ (Γ ∷ A)   zero    = refl
lookup-gr-wkʳ (Γ ∷ A)   (suc i) = lookup-gr-wkʳ Γ i
lookup-gr-wkʳ (Γ ⟨ ρ ⟩) i       = cong (_·̂ᵣ wkʳ-r ρ) (lookup-gr-wkʳ Γ i)
lookup-gr-wkʳ (Γ ᴱ̂)     i       = refl

lookup-gr-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
              → lookup-gr (wkᵉ-ctx Γ) i ≡ wkᵉ-r (lookup-gr Γ i)
lookup-gr-wkᵉ (Γ ∷ A)   zero    = refl
lookup-gr-wkᵉ (Γ ∷ A)   (suc i) = lookup-gr-wkᵉ Γ i
lookup-gr-wkᵉ (Γ ⟨ ρ ⟩) i       = cong (_·̂ᵣ wkᵉ-r ρ) (lookup-gr-wkᵉ Γ i)
lookup-gr-wkᵉ (Γ ᴱ̂)     i       = refl

lookup-crosses-wkᵗ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
                   → lookup-crosses (wkᵗ-ctx Γ) i ≡ lookup-crosses Γ i
lookup-crosses-wkᵗ (Γ ∷ A)   zero    = refl
lookup-crosses-wkᵗ (Γ ∷ A)   (suc i) = lookup-crosses-wkᵗ Γ i
lookup-crosses-wkᵗ (Γ ⟨ ρ ⟩) i       = lookup-crosses-wkᵗ Γ i
lookup-crosses-wkᵗ (Γ ᴱ̂)     i       = refl

lookup-crosses-wkʳ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
                   → lookup-crosses (wkʳ-ctx Γ) i ≡ lookup-crosses Γ i
lookup-crosses-wkʳ (Γ ∷ A)   zero    = refl
lookup-crosses-wkʳ (Γ ∷ A)   (suc i) = lookup-crosses-wkʳ Γ i
lookup-crosses-wkʳ (Γ ⟨ ρ ⟩) i       = lookup-crosses-wkʳ Γ i
lookup-crosses-wkʳ (Γ ᴱ̂)     i       = refl

lookup-crosses-wkᵉ : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
                   → lookup-crosses (wkᵉ-ctx Γ) i ≡ lookup-crosses Γ i
lookup-crosses-wkᵉ (Γ ∷ A)   zero    = refl
lookup-crosses-wkᵉ (Γ ∷ A)   (suc i) = lookup-crosses-wkᵉ Γ i
lookup-crosses-wkᵉ (Γ ⟨ ρ ⟩) i       = lookup-crosses-wkᵉ Γ i
lookup-crosses-wkᵉ (Γ ᴱ̂)     i       = refl

--------------------------------------------------------------
-- The crossing flag of a looked-up variable                 --
--------------------------------------------------------------

crossesᴱ̂-lookup : ∀ {Θ n} → (Γ : OCtx Θ n) → (i : Fin n)
                → crossesᴱ̂ (lookup-var Γ i) ≡ lookup-crosses Γ i
crossesᴱ̂-lookup (Γ ∷ A)   zero    = refl
crossesᴱ̂-lookup (Γ ∷ A)   (suc i) = crossesᴱ̂-lookup Γ i
crossesᴱ̂-lookup (Γ ⟨ ρ ⟩) i       = crossesᴱ̂-lookup Γ i
crossesᴱ̂-lookup (Γ ᴱ̂)     i       = refl

--------------------------------------------------------------
-- Action of a substitution on a membership witness          --
--                                                           --
-- Index-preserving, as `_[_]ᶜᵗˣ` is: the witness is rebuilt  --
-- constructor for constructor, so both its position and its  --
-- crossing flag are untouched.                               --
--------------------------------------------------------------

∈̂-subst : ∀ {Θ Θ' n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
        → (σ : Subst Θ Θ')
        → A ∈̂[ ρ ] Γ
        --------------------------------------------
        → (A [ σ ]ᵛ) ∈̂[ ρ [ σ ]ʳ ] (Γ [ σ ]ᶜᵗˣ)
∈̂-subst σ Hd        = Hd
∈̂-subst σ (Tl-∷ x)  = Tl-∷ (∈̂-subst σ x)
∈̂-subst σ (Tl-⟨⟩ x) = Tl-⟨⟩ (∈̂-subst σ x)
∈̂-subst σ (Tl-ᴱ̂ x)  = Tl-ᴱ̂ (∈̂-subst σ x)

crossesᴱ̂-∈̂-subst : ∀ {Θ Θ' n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                 → (σ : Subst Θ Θ') → (x : A ∈̂[ ρ ] Γ)
                 → crossesᴱ̂ (∈̂-subst σ x) ≡ crossesᴱ̂ x
crossesᴱ̂-∈̂-subst σ Hd        = refl
crossesᴱ̂-∈̂-subst σ (Tl-∷ x)  = crossesᴱ̂-∈̂-subst σ x
crossesᴱ̂-∈̂-subst σ (Tl-⟨⟩ x) = crossesᴱ̂-∈̂-subst σ x
crossesᴱ̂-∈̂-subst σ (Tl-ᴱ̂ x)  = refl

var-pos-∈̂-subst : ∀ {Θ Θ' n} {A : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                → (σ : Subst Θ Θ') → (x : A ∈̂[ ρ ] Γ)
                → var-pos (∈̂-subst σ x) ≡ var-pos x
var-pos-∈̂-subst σ Hd        = refl
var-pos-∈̂-subst σ (Tl-∷ x)  = cong suc (var-pos-∈̂-subst σ x)
var-pos-∈̂-subst σ (Tl-⟨⟩ x) = var-pos-∈̂-subst σ x
var-pos-∈̂-subst σ (Tl-ᴱ̂ x)  = var-pos-∈̂-subst σ x

--------------------------------------------------------------
-- Transporting a membership witness along a type equation   --
--                                                           --
-- The `unbox` rule wants the looked-up type in the shape     --
-- `[ ρ ] A`; the equation that puts it there comes from the  --
-- `_≐ᵥ_` conjunct. Transporting is `J`, so neither position  --
-- nor crossing flag can change.                              --
--------------------------------------------------------------

∈̂-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
           → A ≡ A' → A ∈̂[ ρ ] Γ → A' ∈̂[ ρ ] Γ
∈̂-ty-subst refl x = x

crossesᴱ̂-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                  → (e : A ≡ A') → (x : A ∈̂[ ρ ] Γ)
                  → crossesᴱ̂ (∈̂-ty-subst e x) ≡ crossesᴱ̂ x
crossesᴱ̂-ty-subst refl x = refl

var-pos-ty-subst : ∀ {Θ n} {A A' : OVType Θ} {ρ : RExp Θ} {Γ : OCtx Θ n}
                 → (e : A ≡ A') → (x : A ∈̂[ ρ ] Γ)
                 → var-pos (∈̂-ty-subst e x) ≡ var-pos x
var-pos-ty-subst refl x = refl
