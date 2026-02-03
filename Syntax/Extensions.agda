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

data Ext : Ctx → Ctx → R → Set where
  -- any context is an extension of itself under the correct grade
  id-ext  : ∀ {Γ ρ}       → ctx-grade Γ ≾ᵣ ρ → Ext Γ Γ ρ
  ∷-ext   : ∀ {Γ Γ' A ρ}  → Ext Γ Γ' ρ → Ext Γ (Γ' ∷ A) ρ
  -- ⟨⟩-ext  : ∀ {Γ Γ' ρ ρ'} → Ext Γ Γ' ρ → (ctx-grade Γ' ·ᵣ ρ') ≾ᵣ ρ → Ext Γ (Γ' ⟨ ρ' ⟩) ρ
  -- a renaming context is an extension context:
  ren-ext : ∀ {Γ Γ' ρ}    → Ren Γ Γ' → ctx-grade Γ' ≾ᵣ ρ → Ext Γ Γ' ρ
  -- compositions
  _∘ᵉ_    : ∀ {Γ Γ' Γ'' ρ ρ'} → Ext Γ' Γ'' ρ' → Ext Γ Γ' ρ → Ext Γ Γ'' ρ'
  _∘ᵉʳ_   : ∀ {Γ Γ' Γ'' ρ} → Ren Γ' Γ'' → Ext Γ Γ' ρ → Ext Γ Γ'' ρ

-- The grade of an extension context is a lower bound for the given grade (safety check)

grade-lt-ρ : ∀ {Γ Γ' ρ} → Ext Γ Γ' ρ → ctx-grade Γ' ≾ᵣ ρ
grade-lt-ρ {ρ = ρ} (id-ext rel) = rel
grade-lt-ρ (∷-ext e) = grade-lt-ρ e
-- grade-lt-ρ (⟨⟩-ext e rel) = rel
grade-lt-ρ {Γ' = Γ'} (ren-ext r rel) = rel
grade-lt-ρ (_∘ᵉ_ e' e) = grade-lt-ρ e'
grade-lt-ρ ( _∘ᵉʳ_ r e) = ≾ᵣ-trans (ctx-grade-≾ r) (grade-lt-ρ e)

-- -- Context extensions

-- record Ext (Γ Γ' : Ctx) : Set where
--   constructor ext
--   field
--     ctx-grade-≾ : ctx-grade Γ' ≾ᵣ ctx-grade Γ
--     var-extension : VExt Γ Γ'

-- open Ext public

-- -- Composition of extensions
-- _∘ᵉ_ : ∀ {Γ Γ' Γ''} → Ext Γ' Γ'' → Ext Γ Γ' → Ext Γ Γ''
-- _∘ᵉ_ e e' = ext (≾ᵣ-trans (ctx-grade-≾ e) (ctx-grade-≾ e')) (var-extension e ∘ᵛᵉ var-extension e')

-- -- Compositions of extensions and renamings

-- _∘ʳᵉ_ : ∀ {Γ Γ' Γ''} → Ext Γ' Γ'' → Ren Γ Γ' → Ext Γ Γ''
-- ex ∘ʳᵉ re = ext ((≾ᵣ-trans (ctx-grade-≾ ex) (ctx-grade-≾ re))) (var-extension ex ᵛ∘ʳᵉ var-rename re)

-- _∘ᵉʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ext Γ Γ' → Ext Γ Γ''
-- re ∘ᵉʳ ex = ext (≾ᵣ-trans (ctx-grade-≾ re) (ctx-grade-≾ ex)) (var-rename re ᵛ∘ᵉʳ var-extension ex)

-- id-ext : ∀ {Γ} → Ext Γ Γ
-- id-ext = ext ≾ᵣ-refl id-vext

-- -- -- Equality extension

-- -- eq-ext : ∀ {Γ Γ'} → Γ ≡ Γ' → Ext Γ Γ'
-- -- eq-ext eq = ext (eq-vext eq) {!!}

-- -- -- General congruence extension

-- -- cong-ext : ∀ {Γ Γ' Γ''} → Ext Γ Γ' → Ext (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
-- -- cong-ext {Γ} {Γ'} {Γ''} ex =
-- --   ext (cong-vext {Γ'' = Γ''} (var-extension ex)) {!!}

-- -- -- Variable weakening extension

-- -- wk-∷-ext : ∀ {Γ A} → Ext Γ (Γ ∷ A)
-- -- wk-∷-ext {Γ} {A} =
-- --   ext (wk-∷-vext {Γ} {A}) {!!}

-- -- wk-⟨⟩-ext : ∀ {Γ ρ} → Ext Γ (Γ ⟨ ρ ⟩)
-- -- wk-⟨⟩-ext {Γ} {ρ} =
-- --   ext (wk-⟨⟩-vext {Γ} {ρ}) {!!}

-- -- -- Weakening by a context extension

-- -- wk-ctx-ext : ∀ {Γ Γ'} → Ext Γ (Γ ++ᶜ Γ')
-- -- wk-ctx-ext = ext wk-ctx-vext {!!}

-- -- -- Any context is the extension of the empty context
-- -- empty-ctx-ext : ∀ {Γ} → Ext [] Γ
-- -- empty-ctx-ext {Γ} = ext (empty-ctx-vext {Γ}) {!!}

-- -- A renaming context is an extension context

-- ren⇒ext : ∀ {Γ Γ'} → Ren Γ Γ' → Ext Γ Γ'
-- ren⇒ext re = ext (ctx-grade-≾ re) (vren⇒vext (var-rename re))
