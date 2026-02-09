{-# OPTIONS --allow-unsolved-metas #-} -- remove

------------------------
-- Context extensions --
------------------------

open import Syntax.Grades

module Syntax.Extensions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] )
open Eq.≡-Reasoning

open import Syntax.Extensions.Raw (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Renamings (Grades)

data Ext : Ctx → R → Ctx → Set where
  id-ext : ∀ {Γ ρ} → ρ ≾ᵣ uᵣ → Ext Γ ρ Γ
  ∷-ext : ∀ {Γ Γ' A ρ} → Ext Γ ρ Γ' → Ext Γ ρ (Γ' ∷ A)
  ⟨⟩-ext : ∀ {Γ Γ' ρ ρ'} → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') (Γ' ⟨ ρ' ⟩)

-- The extension context is bound by the sum of the extended context and ρ

grade-lt-ρ : ∀ {Γ Γ' ρ} → Ext Γ ρ Γ' → ctx-grade Γ' ≡ (ctx-grade Γ ·ᵣ ρ)
grade-lt-ρ {Γ} {Γ'} {ρ} (id-ext rel) rewrite c≾ᵣuᵣ⇒c≡uᵣ _ rel = sym (·ᵣ-identityʳ _)
grade-lt-ρ {Γ} {Γ'} {ρ} (∷-ext ex) = grade-lt-ρ ex
grade-lt-ρ {Γ} {Γ'' ⟨ ρ' ⟩} {ρ} (⟨⟩-ext {ρ = ρ''} ex) =
  begin
     ctx-grade (Γ'' ⟨ ρ' ⟩)
   ≡⟨⟩
     ctx-grade Γ'' ·ᵣ ρ'
   ≡⟨ cong (_·ᵣ ρ') (grade-lt-ρ ex) ⟩
     ctx-grade Γ ·ᵣ ρ'' ·ᵣ ρ'
   ≡⟨ ·ᵣ-assoc _ _ _ ⟩
     ctx-grade Γ ·ᵣ (ρ'' ·ᵣ ρ') 
   ∎

-- Composition of extensions

_∘ᵉ_ : ∀ {Γ Γ' Γ'' ρ ρ'} → Ext Γ' ρ' Γ'' → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') Γ''
_∘ᵉ_ {ρ = ρ} (id-ext rel) e rewrite c≾ᵣuᵣ⇒c≡uᵣ _ rel | ·ᵣ-identityʳ ρ = e
_∘ᵉ_ {ρ' = ρ'} (∷-ext e') e = ∷-ext (e' ∘ᵉ e)
_∘ᵉ_ {ρ = ρ} {ρ' = .(ρ₁ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₁} {ρ' = ρ₂} e') e with e' ∘ᵉ e
... | e'' rewrite (sym (·ᵣ-assoc ρ ρ₁ ρ₂)) = ⟨⟩-ext e''

-- Splitting a renaming by an extension

split-ren : ∀ {Γ Γ' Γ'' ρ}
          → Ext Γ'' ρ Γ
          → Ren Γ Γ'
          → Σ[ Γ''' ∈ Ctx ] (Ren Γ'' Γ''' × Σ[ ρ' ∈ R ] ρ' ≾ᵣ ρ × Ext Γ''' ρ' Γ')

split-ren {Γ} {Γ'} {Γ''} {ρ} (id-ext rel) r =
  Γ' , r , ρ , ≾ᵣ-refl , id-ext rel
split-ren {Γ} {Γ'} {Γ''} {ρ} (∷-ext e) r = {!!}
split-ren {Γ} {Γ'} {Γ''} {ρ} (⟨⟩-ext e) r = {!!}

-- Concatenation of extensions

++ᶜ-ext : ∀ {Γ Γ' Γ'' ρ} → Ext Γ ρ Γ' → Ext (Γ'' ++ᶜ Γ) ρ (Γ'' ++ᶜ Γ')
++ᶜ-ext (id-ext rel) = id-ext rel
++ᶜ-ext (∷-ext e)    = ∷-ext (++ᶜ-ext e)
++ᶜ-ext (⟨⟩-ext e)   = ⟨⟩-ext (++ᶜ-ext e)
