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
open import Data.Sum

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
  var-ren     : ∀ {Γ A} → A ∈[ uᵣ ] Γ → Ren (Γ ∷ A) Γ
  -- strong monoidal functor renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → Ren (Γ ⟨ uᵣ ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → Ren Γ (Γ ⟨ uᵣ ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ'  ⟩)
  -- monotonicity renaming for ⟨_⟩ modality
  ⟨⟩-≤-ren    : ∀ {Γ ρ ρ'} → ρ' ≾ᵣ ρ → Ren (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
  -- congruence renamings
  cong-∷-ren  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' ρ} → Ren Γ Γ' → Ren (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)

infixr 20 _∘ʳ_


-- TODO: definitions of natural concrete renamings (see original development)

-- ...

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ'' = []} r         = r
cong-ren {Γ'' = Γ'' ∷ A} r    = cong-∷-ren (cong-ren r)
cong-ren {Γ'' = Γ'' ⟨ ρ' ⟩} r = cong-⟨⟩-ren (cong-ren r)

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren refl = id-ren
 
cong-⟨⟩-≤-ren : ∀ {Γ Γ' ρ ρ'} → Ren Γ Γ' → ρ' ≾ᵣ ρ → Ren (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ' ⟩)
cong-⟨⟩-≤-ren id-ren ρ'≾ρ =
  ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (r₂ ∘ʳ r₁) ρ'≾ρ =
  cong-⟨⟩-≤-ren r₂ ρ'≾ρ ∘ʳ cong-⟨⟩-ren r₁
cong-⟨⟩-≤-ren wk-ren ρ'≾ρ =
  cong-⟨⟩-ren wk-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (var-ren x) ρ'≾ρ =
  cong-⟨⟩-ren (var-ren x) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-η-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-η-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-η⁻¹-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-η⁻¹-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-μ-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-μ-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren ⟨⟩-μ⁻¹-ren ρ'≾ρ =
  cong-⟨⟩-ren ⟨⟩-μ⁻¹-ren ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (⟨⟩-≤-ren rel) ρ'≾ρ =
  cong-⟨⟩-ren (⟨⟩-≤-ren rel) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (cong-∷-ren r) ρ'≾ρ =
  cong-⟨⟩-ren (cong-∷-ren r) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ
cong-⟨⟩-≤-ren (cong-⟨⟩-ren r) ρ'≾ρ =
  cong-⟨⟩-ren (cong-⟨⟩-ren r) ∘ʳ ⟨⟩-≤-ren ρ'≾ρ

cong-renˡ : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ'' ++ᶜ Γ) (Γ'' ++ᶜ Γ')
cong-renˡ id-ren =
  id-ren
cong-renˡ (r₂ ∘ʳ r₁) =
  cong-renˡ r₂ ∘ʳ cong-renˡ r₁
cong-renˡ wk-ren =
  wk-ren
cong-renˡ {Γ' = Γ'} {Γ'' = Γ''} (var-ren x) =
  var-ren (∈-ctx-extensionˡ Γ'' Γ' x)
cong-renˡ ⟨⟩-η-ren =
  ⟨⟩-η-ren
cong-renˡ ⟨⟩-η⁻¹-ren =
  ⟨⟩-η⁻¹-ren
cong-renˡ ⟨⟩-μ-ren =
  ⟨⟩-μ-ren
cong-renˡ ⟨⟩-μ⁻¹-ren =
  ⟨⟩-μ⁻¹-ren
cong-renˡ (⟨⟩-≤-ren x) =
  ⟨⟩-≤-ren x
cong-renˡ (cong-∷-ren r) =
  cong-∷-ren (cong-renˡ r)
cong-renˡ (cong-⟨⟩-ren r) =
  cong-⟨⟩-ren (cong-renˡ r)

-- Weakening a grade to a context renaming

wk-ren-⟨ρ⟩-ctx : ∀ {Γ Γ' ρ} → ctx-grade Γ' ≡ ρ → Ren (Γ ⟨ ρ ⟩) (Γ ++ᶜ Γ')
wk-ren-⟨ρ⟩-ctx {Γ' = []} refl =
  ⟨⟩-η-ren
wk-ren-⟨ρ⟩-ctx {Γ' = Γ' ∷ _} refl =
  wk-ren ∘ʳ wk-ren-⟨ρ⟩-ctx refl
wk-ren-⟨ρ⟩-ctx {Γ} {Γ' ⟨ ρ' ⟩} {ρ} refl =
  cong-⟨⟩-ren (wk-ren-⟨ρ⟩-ctx refl) ∘ʳ ⟨⟩-μ-ren
