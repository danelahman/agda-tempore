------------------------------------------------------------------
-- Sizes                                                         --
--                                                               --
-- `size*` count the nodes of an expression, crossing the sort    --
-- boundaries: the size of a type counts the nodes of the grade   --
-- expressions inside it.                                         --
--                                                               --
-- `Sz` is the size of a scope — the total number of variables it --
-- binds, in all three sorts. Each of the three extensions adds   --
-- exactly one, which is what makes eliminating a variable a      --
-- descent.                                                       --
------------------------------------------------------------------

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.Size (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import TypeInference.OpenSyntax.Grades S
open import TypeInference.OpenSyntax.Types  S

sizeᵉ : ∀ {Θ} → EExp Θ → ℕ
sizeᵉ (evar i)   = 1
sizeᵉ (econst ε) = 1
sizeᵉ (ε ·̂ₑ ε')  = suc (sizeᵉ ε + sizeᵉ ε')

sizeʳ : ∀ {Θ} → RExp Θ → ℕ
sizeʳ (rvar i)   = 1
sizeʳ (rconst ρ) = 1
sizeʳ (ρ ·̂ᵣ ρ')  = suc (sizeʳ ρ + sizeʳ ρ')
sizeʳ ∣ ε ∣̂ᵉ     = suc (sizeᵉ ε)

mutual

  sizeᵛ : ∀ {Θ} → OVType Θ → ℕ
  sizeᵛ (tvar α)  = 1
  sizeᵛ (Base b)  = 1
  sizeᵛ Unit      = 1
  sizeᵛ Bool      = 1
  sizeᵛ (A |×| B) = suc (sizeᵛ A + sizeᵛ B)
  sizeᵛ Empty     = 1
  sizeᵛ (A ⇒ C)   = suc (sizeᵛ A + sizeᶜ C)
  sizeᵛ ([ ρ ] A) = suc (sizeʳ ρ + sizeᵛ A)

  sizeᶜ : ∀ {Θ} → OCType Θ → ℕ
  sizeᶜ (A ‼ ε) = suc (sizeᵛ A + sizeᵉ ε)

Sz : Scope → ℕ
Sz Θ = nTy Θ + nR Θ + nE Θ

Sz-+ty : (Θ : Scope) → Sz (Θ +ty) ≡ suc (Sz Θ)
Sz-+ty Θ = refl

Sz-+r : (Θ : Scope) → Sz (Θ +r) ≡ suc (Sz Θ)
Sz-+r Θ = cong (_+ nE Θ) (+-suc (nTy Θ) (nR Θ))

Sz-+e : (Θ : Scope) → Sz (Θ +e) ≡ suc (Sz Θ)
Sz-+e Θ = +-suc (nTy Θ + nR Θ) (nE Θ)
