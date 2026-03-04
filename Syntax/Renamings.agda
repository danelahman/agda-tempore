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

-- TODO: definitions of natural concrete renamings (see original development)

-- ...

-- "Time-travelling" operation on renamings

_-ʳ_,_ : ∀ {Γ Γ' Γ''}
       → Ren Γ Γ'
       → (ρ : R)
       → Γ -ᶜ ρ ≈ Γ''
       → Σ[ Γ''' ∈ Ctx ] Γ' -ᶜ ρ ≈ Γ''' × Ren Γ'' Γ'''

id-ren -ʳ ρ , p =
  _ , p , id-ren
(r₂ ∘ʳ r₁) -ʳ ρ , p with r₁ -ʳ ρ , p
... | Γ''' , q , r' with r₂ -ʳ ρ , q
... | Γ'''' , s , r'' =
  Γ'''' , s , r'' ∘ʳ r'
wk-ren -ʳ ρ , p with ρ ≡ᵣ? uᵣ
... | yes refl rewrite -ᶜ-u p =
  _ , -ᶜ-uᵣ refl , wk-ren
... | no ¬q =
  _ , -ᶜ-∷ ¬q p , id-ren
var-ren x -ʳ ρ , p = {!!}
⟨⟩-η-ren -ʳ ρ , p = {!!}
⟨⟩-η⁻¹-ren -ʳ ρ , p = {!!}
⟨⟩-μ-ren -ʳ ρ , p = {!!}
⟨⟩-μ⁻¹-ren -ʳ ρ , p = {!!}
⟨⟩-≤-ren q -ʳ ρ , p = {!!}
cong-∷-ren r -ʳ ρ , p = {!!}
cong-⟨⟩-ren r -ʳ ρ , p = {!!}

infixl 30 _-ʳ_,_


{-
_-ʳ_,_,_ : ∀ {Γ Γ' Γ'' Γ'''}
       → Ren Γ Γ'
       → (ρ : R)
       → Γ -ᶜ ρ ≈ Γ''
       → Γ' -ᶜ ρ ≈ Γ'''
       → Ren Γ'' Γ'''

id-ren -ʳ ρ , p , q rewrite -ᶜ-functional p q =
  id-ren
(r₂ ∘ʳ r₁) -ʳ ρ , p , q with -ᶜ-push-ren r₁ p
... | Γ''' , s =
  (r₂ -ʳ ρ , s , q) ∘ʳ (r₁ -ʳ ρ , p , s)
wk-ren -ʳ ρ , p , q with ρ ≡ᵣ? uᵣ
wk-ren -ʳ ρ , p , q | yes refl rewrite -ᶜ-u p | sym (-ᶜ-u q) =
  wk-ren
(wk-ren -ʳ ρ , p , -ᶜ-uᵣ q) | no ¬s =
  ⊥-elim (¬s q)
(wk-ren -ʳ ρ , p , -ᶜ-∷ q r) | no ¬s rewrite -ᶜ-functional p r =
  id-ren
var-ren x -ʳ ρ , p , q with ρ ≡ᵣ? uᵣ
var-ren x -ʳ ρ , p , q | yes refl rewrite sym (-ᶜ-u p) | -ᶜ-u q =
  var-ren x
(var-ren x -ʳ ρ , -ᶜ-uᵣ p , q) | no ¬s = ⊥-elim (¬s p)
(var-ren x -ʳ ρ , -ᶜ-∷ p q , r) | no ¬s rewrite -ᶜ-functional q r =
  id-ren
⟨⟩-η-ren -ʳ ρ , p , q = {!!}
⟨⟩-η⁻¹-ren -ʳ ρ , p , q = {!!}
⟨⟩-μ-ren -ʳ ρ , p , q = {!!}
⟨⟩-μ⁻¹-ren -ʳ ρ , p , q = {!!}
⟨⟩-≤-ren s -ʳ ρ , p , q = {!!}
cong-∷-ren r -ʳ ρ , p , q = {!!}
cong-⟨⟩-ren r -ʳ ρ , p , q = {!!}

infixl 30 _-ʳ_,_,_

-}
