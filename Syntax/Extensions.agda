------------------------
-- Context extensions --
------------------------

open import Syntax.Grades

module Syntax.Extensions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

open import Syntax.Extensions.Raw (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Renamings (Grades)

data Ext : Ctx → R → Ctx → Set where
  id-ext : ∀ {Γ} → Ext Γ uᵣ Γ
  ∷-ext : ∀ {Γ Γ' A ρ} → Ext Γ ρ Γ' → Ext Γ ρ (Γ' ∷ A)
  ⟨⟩-ext : ∀ {Γ Γ' ρ ρ'} → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') (Γ' ⟨ ρ' ⟩)
  _∘ᵉʳ_ : ∀ {Γ Γ' Γ'' ρ} → Ren Γ' Γ'' → Ext Γ ρ Γ' → Ext Γ ρ Γ''

-- The extension context is bound by the sum of the extended context and ρ
-- Note: the case _∘ᵉʳ_ needed for actions of renamings requires to be a difference
-- and not an equivalence.

grade-lt-ρ : ∀ {Γ Γ' ρ} → Ext Γ ρ Γ' → ctx-grade Γ' ≾ᵣ (ctx-grade Γ ·ᵣ ρ) 
grade-lt-ρ {Γ} id-ext =
  ≾ᵣ-reflexive (sym (·ᵣ-identityʳ (ctx-grade Γ)))
  --·ᵣ-identityʳ (ctx-grade Γ)
grade-lt-ρ (∷-ext e) = grade-lt-ρ e
grade-lt-ρ {Γ} {Γ'} {.(ρ ·ᵣ ρ')} (⟨⟩-ext {ρ = ρ} {ρ' = ρ'} e) =
  ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ ρ' (grade-lt-ρ e)) (≾ᵣ-reflexive (·ᵣ-assoc (ctx-grade Γ) ρ ρ'))
  --trans (sym (·ᵣ-assoc (ctx-grade Γ) ρ ρ')) (cong (_·ᵣ ρ') (grade-lt-ρ e))
grade-lt-ρ (_∘ᵉʳ_ r e) =
  ≾ᵣ-trans (ctx-grade-≾ r) (grade-lt-ρ e)
