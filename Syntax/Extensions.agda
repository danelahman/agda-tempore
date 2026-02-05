{-# OPTIONS --allow-unsolved-metas #-} -- remove

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

-- The extension context is bound by the sum of the extended context and ρ

grade-lt-ρ : ∀ {Γ Γ' ρ} → Ext Γ ρ Γ' → ctx-grade Γ' ≾ᵣ (ctx-grade Γ ·ᵣ ρ) 
grade-lt-ρ {Γ} id-ext =
  ≾ᵣ-reflexive (sym (·ᵣ-identityʳ (ctx-grade Γ)))
grade-lt-ρ (∷-ext e) = grade-lt-ρ e
grade-lt-ρ {Γ} {Γ'} {.(ρ ·ᵣ ρ')} (⟨⟩-ext {ρ = ρ} {ρ' = ρ'} e) =
  ≾ᵣ-trans (·ᵣ-monoˡ-≾ᵣ ρ' (grade-lt-ρ e)) (≾ᵣ-reflexive (·ᵣ-assoc (ctx-grade Γ) ρ ρ'))

-- Composition of extensions

_∘ᵉ_ : ∀ {Γ Γ' Γ'' ρ ρ'} → Ext Γ' ρ' Γ'' → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') Γ''
_∘ᵉ_ {ρ = ρ} id-ext e rewrite ·ᵣ-identityʳ ρ = e
_∘ᵉ_ {ρ' = ρ'} (∷-ext e') e = ∷-ext (e' ∘ᵉ e)
_∘ᵉ_ {ρ = ρ} {ρ' = .(ρ₁ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₁} {ρ' = ρ₂} e') e with e' ∘ᵉ e
... | e'' rewrite (sym (·ᵣ-assoc ρ ρ₁ ρ₂)) = ⟨⟩-ext e''

-- Composition of renamings and extensions

_∘ᵉʳ_,_ : ∀ {Γ Γ' Γ'' ρ}
        → Ext Γ'' ρ Γ
        → Ren Γ Γ'
        → ctx-grade Γ' ≾ᵣ ρ
        → Σ[ Γ''' ∈ Ctx ] (Ren Γ'' Γ''' × Σ[ ρ' ∈ R ] ρ' ≾ᵣ ρ × Ext Γ''' ρ Γ')

e ∘ᵉʳ r , rel = {!!}
