-- {-# OPTIONS --allow-unsolved-metas #-} -- (remove)

--------------------------------------------------------------
-- Context renamings                                        --
--                                                          --
-- Note: These are raw (underlying) renamings that are      --
-- further refined in Syntax.Renamings to respect ctx-grade --
--------------------------------------------------------------

open import Syntax.Grades

module Syntax.Renamings (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] ) 

-- Variable renamings (as the smallest relation closed under
-- identities, composition, congruences, ordinary variable 
-- renamings, and strong monoidal functor sturcture for ⟨_⟩)

data Ren : Ctx → Ctx → Set where
  -- identity renaming
  id-ren      : ∀ {Γ} → Ren Γ Γ
  -- composition of renamings
  _∘ʳ_        : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
  -- weakening renaming
  wk-ren      : ∀ {Γ A} → Ren Γ (Γ ∷ A)
  -- variable renaming (corresponds to contraction)
  var-ren     : ∀ {Γ A} → A ∈[ uᵣ ] Γ → Ren (Γ ∷ A) Γ                -- TODO: in non-expring setting this was for general ρ
  -- strong monoidal functor renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → Ren (Γ ⟨ uᵣ ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → Ren Γ (Γ ⟨ uᵣ ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ'  ⟩)
  -- monotonicity renaming for 
  ⟨⟩-≤-ren    : ∀ {Γ ρ ρ'} → ρ' ≾ᵣ ρ → Ren (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
  -- congruence renamings ⟨_⟩ modality
  cong-∷-ren  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' ρ} → Ren Γ Γ' → Ren (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)

infixr 20 _∘ʳ_

-- TODO: natural concrete renamings

-- "Time-travelling" operation on renamings

_-ʳ_,_,_ : ∀ {Γ Γ' Γ'' Γ'''}
       → Ren Γ Γ'
       → (ρ : R)
       → Γ -ᶜ ρ ≈ Γ''
       → Γ' -ᶜ ρ ≈ Γ'''
       → Ren Γ'' Γ'''

id-ren -ʳ ρ , p , q rewrite -ᶜ-functional p q =
  id-ren
(r₂ ∘ʳ r₁) -ʳ ρ , p , q = {!!}
wk-ren -ʳ ρ , p , q = {!!}
var-ren x -ʳ ρ , p , q = {!!}
⟨⟩-η-ren -ʳ ρ , p , q = {!!}
⟨⟩-η⁻¹-ren -ʳ ρ , p , q = {!!}
⟨⟩-μ-ren -ʳ ρ , p , q = {!!}
⟨⟩-μ⁻¹-ren -ʳ ρ , p , q = {!!}
⟨⟩-≤-ren s -ʳ ρ , p , q = {!!}
cong-∷-ren r -ʳ ρ , p , q = {!!}
cong-⟨⟩-ren r -ʳ ρ , p , q = {!!}

infixl 30 _-ʳ_,_,_
