-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Syntax.Grades

module Syntax.Substitutions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Function using (case_of_)

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] )
open Eq.≡-Reasoning
open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Extensions (Grades)
open import Syntax.Language (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

-- Checking whether a variable in a context Γ belongs to the context Γ extends

---- If the variable is in the context before its extension
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
var-in-ctx-prev-ext? (∷-ext e) Hd =
  no (λ { (_ , Hd , refl , id-ext) → ext-decrease-contradiction (λ { () }) e })
var-in-ctx-prev-ext? (∷-ext e) (Tl-∷ x) with var-in-ctx-prev-ext? e x
... | yes (ρ₁ , y , eq , e') = yes (ρ₁ , y , eq , ∷-ext e')
... | no ¬p =
  no (λ { (ρ₁ , y , eq , e') →
        case inv-ext-∷ e' of λ {
          (inj₁ (refl , eq-ctx , refl)) → id-ext-split-≢-contradiction-∷ x y eq eq-ctx e;
          (inj₂ e'') → ¬p (ρ₁ , y , eq , e'') } })
var-in-ctx-prev-ext? {Γ} {Γ' ⟨ ρ₂ ⟩} {A} {ρ'} {ρ} (⟨⟩-ext {ρ = ρ₄} e) (Tl-⟨⟩ x)
  with var-in-ctx-prev-ext? e x
... | yes (ρ₁ , y , eq , e') = yes (ρ₁ , y , eq , ⟨⟩-ext e')
... | no ¬p =
  no (λ { (ρ₁ , y , eq , e') →
        case inv-ext-⟨⟩ e' of λ {
          (inj₁ (eq-grades , eq-ctxs , eq-exts))
            → id-ext-split-≢-contradiction-⟨⟩ x y eq eq-ctxs (ext-≡-grade e (c·ᵣd≡uᵣ⇒c≡uᵣ (sym eq-grades)));
          (inj₂ (_ , e'' , eq-grades)) → ¬p (ρ₁ , y , eq , ext-≡-grade e'' (sym (c·ᵣd≡e·ᵣd⇒c≡e eq-grades))) }})

---- If the variable is not in the context before the extension

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

⟨_,_⟩[_↦_]var : ∀ {Γ A B ρ ρ'}
          → B ∈[ ρ' ] Γ
          → ρ' ≡ uᵣ
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

⟨ Hd , p ⟩[ Hd ↦ W ]var = W
⟨ Hd , p ⟩[ Tl-∷ x ↦ W ]var = var Hd
⟨ Tl-∷ y , refl ⟩[ Hd ↦ W ]var = var y
⟨ Tl-∷ y , p ⟩[ Tl-∷ x ↦ W ]var = V-rename wk-ren ⟨ y , p ⟩[ x ↦ W ]var
⟨ Tl-⟨⟩ y , p ⟩[ Tl-⟨⟩ x ↦ W ]var with c·ᵣd≡uᵣ⇒c≡uᵣ p | c·ᵣd≡uᵣ⇒d≡uᵣ p
... | refl | refl = V-rename ⟨⟩-η⁻¹-ren ⟨ y , refl ⟩[ x ↦ W ]var

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B ρ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  var y       [ x ↦ W ]v = ⟨ y , refl ⟩[ x ↦ W ]var
  const c     [ x ↦ W ]v = const c
  ⦉ V₁ , V₂ ⦊  [ x ↦ W ]v = ⦉ V₁ [ x ↦ W ]v , V₂ [ x ↦ W ]v ⦊
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
