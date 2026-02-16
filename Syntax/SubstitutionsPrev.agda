-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Syntax.Grades

module Syntax.SubstitutionsPrev (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Function using (case_of_)

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Extensions (Grades)
open import Syntax.Language (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

---- Move to extensions:
-- extensions don't decrease contexts
postulate
  ext-decrease-contradiction-∷ : ∀ {Γ A ρ} → Ext (Γ ∷ A) ρ Γ → ⊥

ext-≡-grade : ∀ {Γ Γ' ρ ρ'} → Ext Γ ρ Γ' → ρ ≡ ρ' → Ext Γ ρ' Γ'
ext-≡-grade id-ext eq rewrite (sym eq) =
  id-ext
ext-≡-grade (∷-ext e) eq =
  ∷-ext (ext-≡-grade e eq)
ext-≡-grade (⟨⟩-ext e) eq rewrite (sym eq) =
  ⟨⟩-ext (ext-≡-grade e (c·ᵣd≡e·ᵣd⇒c≡e (trans eq (sym eq))))

-- Inversion lemmas

inv-ext-∷ : ∀ {Γ ρ Γ' A} 
          → Ext Γ ρ (Γ' ∷ A) 
          → (ρ ≡ uᵣ) × (Γ ≡ Γ' ∷ A) ⊎ (Ext Γ ρ Γ')
inv-ext-∷ id-ext    = inj₁ (refl , refl)
inv-ext-∷ (∷-ext e) = inj₂ e

inv-ext-⟨⟩ : ∀ {Γ ρ Γ' ρ'} 
           → Ext Γ ρ (Γ' ⟨ ρ' ⟩) 
           →   (ρ ≡ uᵣ × (Γ ≡ Γ' ⟨ ρ' ⟩))
             ⊎ (Σ[ ρ'' ∈ R ] (Ext Γ ρ'' Γ' × (ρ ≡ ρ'' ·ᵣ ρ' )))
inv-ext-⟨⟩ id-ext     = inj₁ (refl , refl)
inv-ext-⟨⟩ (⟨⟩-ext e) = inj₂ (_ , e , refl)

var-in-ctx-not-in-ctx-contradiction :
  ∀ {Γ A B ρ}
  → (x : A ∈[ ρ ] Γ ∷ B)
  → ¬(Σ[ ρ' ∈ R ] Σ[ y ∈ (A ∈[ ρ' ] Γ ∷ B) ]
       (proj₁ (var-split y) ≡ proj₁ (var-split x))
     × (Ext (proj₁ (proj₂ (var-split y))) uᵣ (proj₁ (proj₂ (var-split x))))) → ⊥
var-in-ctx-not-in-ctx-contradiction {ρ = ρ} x ¬p = ¬p (ρ , x , refl , id-ext)

-- Remove?

ext-diff-sizes-contradiction : ∀ {Γ ρ} → Ext Γ ρ [] → ¬ (Γ ≡ []) → ⊥
ext-diff-sizes-contradiction id-ext neq = neq refl

---- Checking whether a variable in a context Γ belongs to the context Γ extends

-- If the variable is in the context before its extension
var-in-ctx-prev-ext? :
  ∀ {Γ Γ' A ρ' ρ}
  → Ext Γ ρ' Γ'
  → (x : A ∈[ ρ ] Γ')
  → Dec
    (Σ[ ρ₁ ∈ R ]
        Σ[ y ∈ A ∈[ ρ₁ ] Γ ]
           ( proj₁ (var-split y) ≡ proj₁ (var-split x)
           × Ext (proj₁ (proj₂ (var-split y))) ρ'
                 (proj₁ (proj₂ (var-split x)))
           )
        )

var-in-ctx-prev-ext? id-ext x = yes (_ , x , refl , id-ext)
var-in-ctx-prev-ext? (∷-ext e) Hd = no (λ { (_ , Hd , refl , id-ext) → ext-decrease-contradiction-∷ e })
var-in-ctx-prev-ext? (∷-ext e) (Tl-∷ x) with var-in-ctx-prev-ext? e x
... | yes (ρ₁ , y , eq , e') = yes (ρ₁ , y , eq , ∷-ext e')
var-in-ctx-prev-ext? {[]} {Γ' ∷ B} {ρ' = ρ'} {ρ = ρ} (∷-ext e) (Tl-∷ x) | no ¬p =
  no λ ()
var-in-ctx-prev-ext? {Γ ∷ C} {Γ' ∷ B} {A} {ρ' = ρ'} {ρ = ρ} (∷-ext e) (Tl-∷ x) | no ¬p =
  no λ where
       (.(uᵣ) , Hd , eq , ∷-ext e') → ¬p (uᵣ , Hd , eq , e')
       (ρ₁ , Tl-∷ y , eq , e') →
         case inv-ext-∷ e' of λ where
           (inj₁ (refl , eq')) →
             let eq-ctxs = ∷ᶜ-injective-ctx eq' in
               let eq-types = ∷ᶜ-injective-ty eq' in
                 {!!}
                   
           (inj₂ e'') → ¬p (ρ₁ , Tl-∷ y , eq , e'')
var-in-ctx-prev-ext? {Γ ⟨ ρ₂ ⟩} {Γ' ∷ B} {ρ' = ρ'} {ρ = ρ} (∷-ext e) (Tl-∷ x) | no ¬p =
  no λ where
     (ρ₁ , Tl-⟨⟩ y , eq , ∷-ext e') → ¬p (ρ₁ , Tl-⟨⟩ y , eq , e')
var-in-ctx-prev-ext? {Γ} {Γ' ⟨ ρ₂ ⟩} {A} {ρ'} {ρ} (⟨⟩-ext {ρ = ρ₄} e) (Tl-⟨⟩ x)
  with var-in-ctx-prev-ext? e x
... | yes (ρ₁ , y , eq , e') = yes (ρ₁ , y , eq , ⟨⟩-ext e')
var-in-ctx-prev-ext? {[]} {Γ' ⟨ ρ₂ ⟩} {A} {.((_ ·ᵣ_) ρ₂)} {.((_ ·ᵣ_) ρ₂)} (⟨⟩-ext {ρ = _} e) (Tl-⟨⟩ x) | no ¬p =
  no λ ()
var-in-ctx-prev-ext? {Γ ∷ C} {Γ' ⟨ ρ₂ ⟩} {A} {.(ρ₃ ·ᵣ ρ₂)} {.(ρ₄ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₃} e) (Tl-⟨⟩ {ρ' = ρ₄} x) | no ¬p = 
  no λ where
     (.(uᵣ) , Hd , eq , e') →
       case inv-ext-⟨⟩ e' of λ where
            (inj₂ (ρ , e'' , eq')) →
                  ¬p (uᵣ , Hd , eq , ext-≡-grade e'' (sym (c·ᵣd≡e·ᵣd⇒c≡e eq')))
     (ρ₁ , Tl-∷ y , eq , e') →
       case inv-ext-⟨⟩ e' of λ where
            (inj₂ (ρ₇ , e'' , eq')) →
              ¬p (ρ₁ , Tl-∷ y  , eq , ext-≡-grade e'' (sym (c·ᵣd≡e·ᵣd⇒c≡e eq')))
var-in-ctx-prev-ext? {Γ ⟨ ρ₅ ⟩} {Γ' ⟨ ρ₂ ⟩} {A} {.(ρ₃ ·ᵣ ρ₂)} {.(ρ₄ ·ᵣ ρ₂)} (⟨⟩-ext {ρ = ρ₃} e) (Tl-⟨⟩ {ρ' = ρ₄} x) | no ¬p =
  no λ where
     (ρ₁ , Tl-⟨⟩ y , eq , e') →
       case inv-ext-⟨⟩ e' of λ where
         (inj₁ (eq' , eqSplit)) → {!!}
         (inj₂ (ρ , e'' , eq')) →
               ¬p (ρ₁ , Tl-⟨⟩ y , eq , ext-≡-grade e'' (sym (c·ᵣd≡e·ᵣd⇒c≡e eq')))

-- If the variable is not in the context before the extension

var-not-in-ctx-prev-ext : ∀ {Γ Γ' A ρ ρ'}
                        → Ext Γ ρ Γ'
                        → (x : A ∈[ ρ' ] Γ')
                        → ¬ (Σ[ ρ'' ∈ R ] Σ[ y ∈ A ∈[ ρ'' ] Γ ]
                              ( proj₁ (var-split y) ≡ proj₁ (var-split x)
                              × Ext (proj₁ (proj₂ (var-split y))) ρ (proj₁ (proj₂ (var-split x)))
                              )
                            )
                        → Ext Γ ρ (proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)))

var-not-in-ctx-prev-ext {ρ' = ρ'} id-ext x   ¬p = ⊥-elim (¬p (ρ' , x , refl , id-ext))
var-not-in-ctx-prev-ext (∷-ext e) Hd         ¬p = e
var-not-in-ctx-prev-ext (∷-ext e) (Tl-∷ x)   ¬p =
  ∷-ext (var-not-in-ctx-prev-ext e x (λ where (ρ₁ , y , eq , e') → ¬p (ρ₁ , y , eq , ∷-ext e')))
var-not-in-ctx-prev-ext (⟨⟩-ext e) (Tl-⟨⟩ x) ¬p =
  ⟨⟩-ext (var-not-in-ctx-prev-ext e x (λ where (ρ₁ , y , eq , e') → ¬p (ρ₁ , y , eq , ⟨⟩-ext e')))

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
Tl-⟨⟩ y [ Tl-⟨⟩ x ↦ W ]var = {!!}

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
    (unbox {Γ' = Γ'} {ρ = ρ'} {ρ' = ρ''} e rel V M) x W with var-in-ctx-prev-ext? e x
  ... | yes (_ , y , eq , ex') =
    unbox
      (++ᶜ-ext ex')
      rel
      (V-rename
        (cong-ren {Γ = proj₁ (var-split y)} {Γ' = proj₁ (var-split x)} {Γ'' = proj₁ (proj₂ (var-split y))}
          (eq-ren eq))
        (V [ y ↦ V-rename (eq-ren (sym eq)) W ]v))
      (M [ Tl-∷ x ↦ W ]c)
  ... | no ¬p =
    unbox
      (var-not-in-ctx-prev-ext e x ¬p)
      rel
      V
      (M [ Tl-∷ x ↦ W ]c)

  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce M rel [ x ↦ W ]c = coerce (M [ x ↦ W ]c) rel
