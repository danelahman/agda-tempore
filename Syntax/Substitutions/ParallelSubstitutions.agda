----------------------------
-- Parallel substitutions --
----------------------------

open import Syntax.Grades

module Syntax.Substitutions.ParallelSubstitutions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)

-- Substitutions in terms

Sub : Ctx → Ctx → Set
Sub Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ Γ₁ Γ₂ ∈ Ctx ] (Ren (Γ₁ ++ᶜ Γ₂) Γ' × Γ₁ ⊢V⦂ A × ρ ≾ᵣ ctx-grade Γ₂)
