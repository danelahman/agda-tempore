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

-- TODO move to another file

c≺u-contradiction : ∀ {ρ} → (ρ ≺ᵣ uᵣ) → ⊥
c≺u-contradiction r = {!!}

---- Deciding whether a variable was in the context before the extension

-- If the variable is in the context before its extension

var-in-ctx-prev-ext : ∀ {Γ Γ' A ρ' ρ}
                    → Ext Γ ρ' Γ'
                    → (x : A ∈[ ρ ] Γ')
                    → ρ ≾ᵣ ρ'
                    → Σ[ ρ'' ∈ R ] (
                         ρ'' ≾ᵣ ρ
                       × Σ[ y ∈ A ∈[ ρ'' ] Γ ]
                           (proj₁ (var-split y)) ≡ (proj₁ (var-split x))
                         × Ext (proj₁ (proj₂ (var-split y))) ρ' (proj₁ (proj₂ (var-split x))) )

var-in-ctx-prev-ext {ρ = ρ} id-ext x rel rewrite (c≾ᵣuᵣ⇒c≡uᵣ ρ rel) =
  uᵣ , uᵣ≾ᵣc , x , refl , id-ext
var-in-ctx-prev-ext (∷-ext e) Hd rel =       -- this case is impossible, as it means that x is immediately
  ⊥-elim {!!}                                -- available in Γ', implying it should be part of the extension of Γ.
var-in-ctx-prev-ext (∷-ext e) (Tl-∷ x) rel with var-in-ctx-prev-ext e x rel
... | ρ'' , rel' , y , eq , e' = ρ'' , rel' , y , eq , ∷-ext e'
var-in-ctx-prev-ext {Γ' = Γ' ⟨ ρ₂ ⟩} {ρ' = .(ρ₁ ·ᵣ ρ₂)} {ρ = .(ρ₃ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₁} {ρ' = ρ₂} e) (Tl-⟨⟩ {ρ' = ρ₃} x) rel
  with var-in-ctx-prev-ext e x (c·ᵣd≾ᵣe·d⇒c≾ᵣe rel)
... | ρ'' , rel' , y , eq , e' =
  ρ'' , ≾ᵣ-trans rel' (ρ-≾ᵣ-substₗ (·ᵣ-identityʳ ρ₃) (·ᵣ-monoʳ-≾ᵣ ρ₃ uᵣ≾ᵣc)) , y , eq , ⟨⟩-ext e'

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
    (unbox {Γ' = Γ'} {ρ = ρ'} {ρ' = ρ''} e rel V M) x W with ρ ≾ᵣ? ρ''
  _[_↦_]c (unbox {Γ' = Γ'} {ρ = ρ'} {ρ' = ρ''} e rel V M) x W | yes p with var-in-ctx-prev-ext e x p
  ... | ̂p , rel' , y , eq , e' =
    unbox
      (++ᶜ-ext e')
      rel
      (V-rename
        (cong-ren {Γ = proj₁ (var-split y)} {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split y))}
          (eq-ren eq))
        (V [ y ↦ V-rename (eq-ren (sym eq)) W ]v))
      (M [ Tl-∷ x ↦ W ]c)
  _[_↦_]c (unbox {Γ' = Γ'} {ρ = ρ'} {ρ' = ρ''} e rel V M) x W | no ¬p =
    unbox
      (var-not-in-ctx-prev-ext e x (¬≾ᵣ⇒≻ᵣflip ¬p))
      rel
      V -- (V-rename (proj₂ (proj₂ (var-not-in-ctx-prev-ext e x (¬≾ᵣ⇒≻ᵣflip ¬p)))) V)
      (M [ Tl-∷ x ↦ W ]c)

  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce M rel [ x ↦ W ]c = coerce (M [ x ↦ W ]c) rel
