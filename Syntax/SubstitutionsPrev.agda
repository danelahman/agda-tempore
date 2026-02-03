-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Syntax.Grades

module Syntax.SubstitutionsPrev (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Types (Grades)
open import Syntax.Extensions (Grades)

open import Syntax.RenActions (Grades)

open import Util.Equality
open import Util.Time -- remove

-- Deciding whether a variable was in the context before the extension

{-
var-in-ctx-prev-ext : ∀ {Γ Γ' A ρ ρ'}
                    → Ext Γ' Γ ρ'
                    → (x : A ∈[ ρ ] Γ)
                    → ρ' ≾ᵣ ctx-grade Γ' -- This condition is not correct.
                    → Σ[ y ∈ A ∈[ (ρ ·ᵣ ρ') ] Γ' ]
                       (  (Ren (proj₁ (var-split y)) (proj₁ (var-split x) ))
                        × Ren (proj₁ (proj₂ (var-split y))) (proj₁ (proj₂ (var-split x))))
-}

-- If the variable is not in the context before the extension

{-
var-not-in-ctx-prev-ext : ∀ {Γ Γ' A ρ ρ'}
                       → Ext Γ Γ' ρ'
                       → (x : A ∈[ ρ ] Γ')
                       → ctx-grade Γ ≾ᵣ ρ' -- check condition: x occurs "after" the blocking time
                       → Ren Γ (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)))
-}

-- Substituting a value for a variable in context

_[_↦_]var : ∀ {Γ A B ρ}
          → B ∈[ uᵣ ] Γ
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          ---------------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

Hd [ Hd ↦ W ]var = W
Hd [ Tl-∷ x ↦ W ]var = var Hd
Tl-∷ y [ Hd ↦ W ]var = var y
Tl-∷ y [ Tl-∷ x ↦ W ]var = V-rename wk-ren (y [ x ↦ W ]var)
Tl-⟨⟩ y [ x ↦ W ]var = {!!}

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B ρ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  var y       [ x ↦ W ]v = y [ x ↦ W ]var
  const c     [ x ↦ W ]v = const c
  ⦉ V₁ , V₂ ⦊ [ x ↦ W ]v = ⦉ V₁ [ x ↦ W ]v , V₂ [ x ↦ W ]v ⦊
  ⋆           [ x ↦ W ]v = ⋆
  lam M       [ x ↦ W ]v = lam (M [ Tl-∷ x ↦ W ]c)

  _[_↦_]c : ∀ {Γ A C ρ}
          → Γ ⊢C⦂ C
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢C⦂ C

  return V        [ x ↦ W ]c = return (V [ x ↦ W ]v)
  (M ; N)         [ x ↦ W ]c  = (M [ x ↦ W ]c) ; (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂)       [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  (match V `in N) [ x ↦ W ]c = match V [ x ↦ W ]v `in (N [ Tl-∷ (Tl-∷ x) ↦ W ]c)
  absurd V        [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M  [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  delay τ M       [ x ↦ W ]c = delay τ (M [ Tl-⟨⟩ x ↦ W ]c)
  handle M `with H `in N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with  (λ op ρ'' → (H op ρ'') [ Tl-∷ (Tl-∷ x) ↦ W ]c)
    `in    (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c {Γ = Γ} {A = A} {ρ = ρ}
    (unbox {Γ' = Γ'} {ρ = ρ'} e rel V M) x W = {!!}

  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce M rel [ x ↦ W ]c = coerce (M [ x ↦ W ]c) rel
