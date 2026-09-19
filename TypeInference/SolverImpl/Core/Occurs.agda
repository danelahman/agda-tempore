------------------------------------------------------------------
-- Occurrence of a variable, and strengthening along it          --
--                                                               --
-- `occ*` say whether a variable of one of the three sorts occurs --
-- syntactically in an expression of one of the four categories.  --
-- The sorts are stratified — effect expressions contain neither  --
-- resource-grade nor type variables, resource expressions no     --
-- type variables — so the traversals that cross a sort boundary  --
-- (`∣_∣̂ᵉ`, `[_]_`, `_‼_`) are the only ones that can report an   --
-- occurrence, and the remaining cross-sort cases are constantly  --
-- `false`.                                                      --
--                                                               --
-- `chk*` combine the check with the renaming: an expression in   --
-- which the variable does not occur is one of the smaller scope, --
-- and the single-binding substitution of `Core.For` computes the --
-- renaming, its image being immaterial.                          --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; _∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe.Base using (Maybe; just; nothing)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.Occurs (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S
open import TypeInference.Open.Subst  S

open import TypeInference.SolverImpl.Core.For S

mutual

  occᵗ-v : ∀ {Θ} → TyVar Θ → OVType Θ → 𝔹
  occᵗ-v α (tvar β)  = ⌊ α ≟ᶠ β ⌋
  occᵗ-v α (Base b)  = false
  occᵗ-v α Unit      = false
  occᵗ-v α Bool      = false
  occᵗ-v α (A |×| B) = occᵗ-v α A ∨ occᵗ-v α B
  occᵗ-v α Empty     = false
  occᵗ-v α (A ⇒ C)   = occᵗ-v α A ∨ occᵗ-c α C
  occᵗ-v α ([ ρ ] A) = occᵗ-v α A

  occᵗ-c : ∀ {Θ} → TyVar Θ → OCType Θ → 𝔹
  occᵗ-c α (A ‼ ε) = occᵗ-v α A

occʳ-r : ∀ {Θ} → RVar Θ → RExp Θ → 𝔹
occʳ-r i (rvar j)   = ⌊ i ≟ᶠ j ⌋
occʳ-r i (rconst ρ) = false
occʳ-r i (ρ ·̂ᵣ ρ')  = occʳ-r i ρ ∨ occʳ-r i ρ'
occʳ-r i ∣ ε ∣̂ᵉ     = false

mutual

  occʳ-v : ∀ {Θ} → RVar Θ → OVType Θ → 𝔹
  occʳ-v i (tvar β)  = false
  occʳ-v i (Base b)  = false
  occʳ-v i Unit      = false
  occʳ-v i Bool      = false
  occʳ-v i (A |×| B) = occʳ-v i A ∨ occʳ-v i B
  occʳ-v i Empty     = false
  occʳ-v i (A ⇒ C)   = occʳ-v i A ∨ occʳ-c i C
  occʳ-v i ([ ρ ] A) = occʳ-r i ρ ∨ occʳ-v i A

  occʳ-c : ∀ {Θ} → RVar Θ → OCType Θ → 𝔹
  occʳ-c i (A ‼ ε) = occʳ-v i A

occᵉ-e : ∀ {Θ} → EVar Θ → EExp Θ → 𝔹
occᵉ-e i (evar j)   = ⌊ i ≟ᶠ j ⌋
occᵉ-e i (econst ε) = false
occᵉ-e i (ε ·̂ₑ ε')  = occᵉ-e i ε ∨ occᵉ-e i ε'

occᵉ-r : ∀ {Θ} → EVar Θ → RExp Θ → 𝔹
occᵉ-r i (rvar j)   = false
occᵉ-r i (rconst ρ) = false
occᵉ-r i (ρ ·̂ᵣ ρ')  = occᵉ-r i ρ ∨ occᵉ-r i ρ'
occᵉ-r i ∣ ε ∣̂ᵉ     = occᵉ-e i ε

mutual

  occᵉ-v : ∀ {Θ} → EVar Θ → OVType Θ → 𝔹
  occᵉ-v i (tvar β)  = false
  occᵉ-v i (Base b)  = false
  occᵉ-v i Unit      = false
  occᵉ-v i Bool      = false
  occᵉ-v i (A |×| B) = occᵉ-v i A ∨ occᵉ-v i B
  occᵉ-v i Empty     = false
  occᵉ-v i (A ⇒ C)   = occᵉ-v i A ∨ occᵉ-c i C
  occᵉ-v i ([ ρ ] A) = occᵉ-r i ρ ∨ occᵉ-v i A

  occᵉ-c : ∀ {Θ} → EVar Θ → OCType Θ → 𝔹
  occᵉ-c i (A ‼ ε) = occᵉ-v i A ∨ occᵉ-e i ε

chkᵗ-v : ∀ {Θ} → TyVar (Θ +ty) → OVType (Θ +ty) → Maybe (OVType Θ)
chkᵗ-v α A = if occᵗ-v α A then nothing else just (A [ Unit forᵗ α ]ᵛ)

chkʳ-r : ∀ {Θ} → RVar (Θ +r) → RExp (Θ +r) → Maybe (RExp Θ)
chkʳ-r i ρ = if occʳ-r i ρ then nothing else just (ρ [ ûᵣ forʳ i ]ʳ)

chkᵉ-e : ∀ {Θ} → EVar (Θ +e) → EExp (Θ +e) → Maybe (EExp Θ)
chkᵉ-e i ε = if occᵉ-e i ε then nothing else just (ε [ ûₑ forᵉ i ]ᵉ)
