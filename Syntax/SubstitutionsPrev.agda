-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Syntax.Grades

module Syntax.SubstitutionsPrev (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Irrelevant
open import Data.Product
open import Data.Unit.Base using (⊤)

open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Types (Grades)
open import Syntax.Extensions (Grades)

open import Syntax.RenActions (Grades)

open import Util.Equality
open import Util.Time -- remove

---- Consequences of a variable being (or not) in the context before the extension

-- If the variable is in the context before its extension
var-in-ctx-prev-ext :
  ∀ {Γ Γ' A ρ' ρ}
  → Ext Γ ρ' Γ'
  → (x : A ∈[ ρ ] Γ')
  → Dec
      (Σ[ ρ₁ ∈ R ]
        Σ[ y ∈ A ∈[ ρ₁ ] Γ ]
          ( ρ₁ ≾ᵣ ρ
          × proj₁ (var-split y) ≡ proj₁ (var-split x)
          × Ext (proj₁ (proj₂ (var-split y))) ρ'
                (proj₁ (proj₂ (var-split x)))
          )
      )

var-in-ctx-prev-ext {[]} e x =
  no λ()
var-in-ctx-prev-ext {Γ' ∷ B} {Γ' ∷ B} {A} {.(uᵣ)} {ρ} id-ext x =
  yes (ρ , x , ≾ᵣ-refl , refl , id-ext)
var-in-ctx-prev-ext {Γ} {Γ' ∷ A} {A} {ρ'} {.(uᵣ)} (∷-ext e) Hd = {!!}
var-in-ctx-prev-ext {Γ ∷ C} {Γ' ∷ B} {A} {ρ'} {ρ} (∷-ext e) (Tl-∷ x)
  with var-in-ctx-prev-ext {Γ ∷ C} {Γ'} e x
... | yes (ρ₁ , y , rel , eq , e') = yes (ρ₁ , y , rel , eq , ∷-ext e')
... | no ¬p with C ≡? A
... | yes q rewrite (sym q) = yes (uᵣ , Hd , uᵣ≾ᵣc , {!!} , ∷-ext {!!})
var-in-ctx-prev-ext {Γ ⟨ ρ₂ ⟩} {Γ' ∷ B} {A} {ρ'} {ρ} (∷-ext e) (Tl-∷ x)
  with var-in-ctx-prev-ext {Γ ⟨ ρ₂ ⟩} {Γ'} e x
... | yes (ρ₁ , y , rel , eq , e') = yes (ρ₁ , y , rel , eq , ∷-ext e')
... | no ¬p = {!!}
var-in-ctx-prev-ext {Γ} {Γ' ⟨ ρ₂ ⟩} {A} {ρ'} {ρ} e x = {!!}

{-
-- If the variable is not in the context before the extension

var-not-in-ctx-prev-ext : ∀ {Γ Γ' A ρ ρ'}
                       → Ext Γ ρ' Γ'
                       → (x : A ∈[ ρ ] Γ')
                       → ρ' ≺ᵣ ρ
                       → Ext Γ ρ' (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)))

var-not-in-ctx-prev-ext id-ext Hd rel = ⊥-elim (c≺u-contradiction rel)
var-not-in-ctx-prev-ext id-ext (Tl-∷ x) rel = {!!}
var-not-in-ctx-prev-ext id-ext (Tl-⟨⟩ {Γ} x) rel = {!!}
var-not-in-ctx-prev-ext (∷-ext e) x rel = {!!}
var-not-in-ctx-prev-ext (⟨⟩-ext e) x rel = {!!}
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
    (unbox {Γ' = Γ'} {ρ = ρ'} {ρ' = ρ''} e rel V M) x W with var-in-ctx-prev-ext e x
  ... | yes (ρ₁ , y , rel' , eq , ex') =
    unbox
      (++ᶜ-ext ex')
      rel
      (V-rename
        (cong-ren {Γ = proj₁ (var-split y)} {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split y))}
          (eq-ren eq))
        (V [ y ↦ V-rename (eq-ren (sym eq)) W ]v))
      (M [ Tl-∷ x ↦ W ]c)
  _[_↦_]c (unbox {Γ' = Γ'} {ρ = ρ'} {ρ' = ρ''} e rel V M) x W | no ¬p =
    unbox
      {!!} --(var-not-in-ctx-prev-ext e x (¬≾ᵣ⇒≻ᵣflip ¬p))
      rel
      V -- (V-rename (proj₂ (proj₂ (var-not-in-ctx-prev-ext e x (¬≾ᵣ⇒≻ᵣflip ¬p)))) V)
      (M [ Tl-∷ x ↦ W ]c)

  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce M rel [ x ↦ W ]c = coerce (M [ x ↦ W ]c) rel
