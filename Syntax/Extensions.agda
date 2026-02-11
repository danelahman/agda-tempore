-- {-# OPTIONS --allow-unsolved-metas #-} -- (remove)

------------------------
-- Context extensions --
------------------------

open import Syntax.Grades

module Syntax.Extensions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product
open import Data.Empty

open import Relation.Binary.Core
open import Relation.Nullary -- Remove?
open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] )
open Eq.≡-Reasoning

open import Syntax.Extensions.Raw (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Renamings (Grades)

-- Context extension

data Ext : Ctx → R → Ctx → Set where
  id-ext : ∀ {Γ} → Ext Γ uᵣ Γ
  ∷-ext : ∀ {Γ Γ' A ρ} → Ext Γ ρ Γ' → Ext Γ ρ (Γ' ∷ A)
  ⟨⟩-ext : ∀ {Γ Γ' ρ ρ'} → Ext Γ ρ Γ' → Ext Γ (ρ ·ᵣ ρ') (Γ' ⟨ ρ' ⟩)

-- The extension context is bound by the sum of the extended context and ρ

grade-lt-ρ : ∀ {Γ Γ' ρ} → Ext Γ ρ Γ' → ctx-grade Γ' ≡ (ctx-grade Γ ·ᵣ ρ)
grade-lt-ρ {Γ} {Γ'} {ρ} id-ext = sym (·ᵣ-identityʳ (ctx-grade Γ))
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
_∘ᵉ_ {ρ = ρ} id-ext e rewrite ·ᵣ-identityʳ ρ = e
_∘ᵉ_ {ρ' = ρ'} (∷-ext e') e = ∷-ext (e' ∘ᵉ e)
_∘ᵉ_ {ρ = ρ} {ρ' = .(ρ₁ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₁} {ρ' = ρ₂} e') e with e' ∘ᵉ e
... | e'' rewrite (sym (·ᵣ-assoc ρ ρ₁ ρ₂)) = ⟨⟩-ext e''

--

{-
left-split-ren : ∀ {Γ Γ' Γ''} → Ren (Γ ++ᶜ Γ') Γ'' → Σ[ Γ₁ ∈ Ctx ] (Σ[ Γ₂ ∈ Ctx ] (Ren Γ Γ₁ × (Γ₁ , Γ₂ split Γ'') ))
left-split-ren {Γ'' = []} r = [] , [] , {!!} , split-[]
left-split-ren {Γ} {Γ'} {Γ'' ∷ A} r with left-split-ren {Γ} {Γ'} {Γ''} {!!}
... | Γ₁ , Γ₂ , r' , s = Γ₁ , Γ₂ ∷ A , r' , split-∷ s
left-split-ren {Γ} {Γ'} {Γ'' ⟨ ρ ⟩} r
  with left-split-ren {Γ} {Γ'} {Γ''} (ren (≾ᵣ-trans (c≾ᵣc·ᵣd {d = ρ}) (ctx-grade-≾ r)) {!!})
... | Γ₁ , Γ₂ , r' , s = Γ₁ , Γ₂ ⟨ ρ ⟩ , r' , split-⟨⟩ s
-}

-- Splitting a renaming by an extension

split-ren : ∀ {Γ Γ' Γ'' ρ}
          → Ext Γ'' ρ Γ
          → Ren Γ Γ'
          → Σ[ Γ''' ∈ Ctx ] (Ren Γ'' Γ''' × Σ[ ρ' ∈ R ] ρ' ≾ᵣ ρ × Ext Γ''' ρ' Γ')

split-ren {Γ} {Γ'} {Γ} {ρ} id-ext r =
  Γ' , r , uᵣ , ≾ᵣ-refl , id-ext
split-ren {Γ ∷ A} {Γ'} {Γ''} {ρ} (∷-ext e) r =
  split-ren {Γ} e (r ∘ʳ wk-ren)
split-ren {Γ ⟨ ρ₂ ⟩} {Γ'} {Γ''} {.(ρ₁ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₁} e) r
  with split-ren e {!r ∘ʳ ?!}
... | Γ''' , r' , ρ' , rel , e' =
  {!!} , {!!} , {!!} , ≾ᵣ-trans (≾ᵣ-reflexive (sym (·ᵣ-identityʳ ρ₁))) (·ᵣ-monoʳ-≾ᵣ ρ₁ uᵣ≾ᵣc) , {!!}

-- Concatenation of extensions

++ᶜ-ext : ∀ {Γ Γ' Γ'' ρ} → Ext Γ ρ Γ' → Ext (Γ'' ++ᶜ Γ) ρ (Γ'' ++ᶜ Γ')
++ᶜ-ext id-ext     = id-ext
++ᶜ-ext (∷-ext e)  = ∷-ext (++ᶜ-ext e)
++ᶜ-ext (⟨⟩-ext e) = ⟨⟩-ext (++ᶜ-ext e)
