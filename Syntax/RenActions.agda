-- {-# OPTIONS --allow-unsolved-metas #-} -- remove

------------------------------------------
-- Renaming actions on well-typed terms --
------------------------------------------

open import Syntax.Grades

module Syntax.RenActions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Language (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

-- Useful substitution of resource annotations

var-ρ-subst : ∀ {Γ A ρ ρ'}
            → ρ ≡ ρ'
            → A ∈[ ρ ] Γ
            → A ∈[ ρ' ] Γ
            
var-ρ-subst refl x = x

-- Renaming of variables

var-rename : ∀ {Γ Γ' A ρ}
           → Ren Γ Γ'
           → A ∈[ ρ ] Γ
           → Σ[ ρ' ∈ R ] (ρ' ≾ᵣ ρ × A ∈[ ρ' ] Γ')
           
var-rename id-ren x =
  _ , ≾ᵣ-refl , x
var-rename (r₂ ∘ʳ r₁) x with var-rename r₁ x
... | ρ' , ρ'≾ρ , y with var-rename r₂ y
... | ρ'' , ρ''≾ρ' , z =
  ρ'' , ≾ᵣ-trans ρ''≾ρ' ρ'≾ρ , z
var-rename wk-ren x =
  _ , ≾ᵣ-refl , Tl-∷ x
var-rename (var-ren y) Hd =
  uᵣ , ≾ᵣ-refl , y
var-rename (var-ren y) (Tl-∷ x) =
  var-rename id-ren x
var-rename ⟨⟩-η-ren (Tl-⟨⟩ x) =
  _ , ≾ᵣ-reflexive (sym (·ᵣ-identityʳ _)) , x
var-rename ⟨⟩-η⁻¹-ren Hd =
  uᵣ ·ᵣ uᵣ , ≾ᵣ-reflexive (·ᵣ-identityʳ uᵣ) , Tl-⟨⟩ Hd
var-rename ⟨⟩-η⁻¹-ren (Tl-∷ x) =
  _ , ≾ᵣ-reflexive (·ᵣ-identityʳ _) , Tl-⟨⟩ (Tl-∷ x)
var-rename ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) =
  _ , ≾ᵣ-reflexive (·ᵣ-identityʳ (_ ·ᵣ _)) , Tl-⟨⟩ (Tl-⟨⟩ x)
var-rename ⟨⟩-μ-ren (Tl-⟨⟩ x) =
  _ , ≾ᵣ-reflexive (·ᵣ-assoc _ _ _) , Tl-⟨⟩ (Tl-⟨⟩ x)
var-rename ⟨⟩-μ⁻¹-ren (Tl-⟨⟩ (Tl-⟨⟩ x)) =
  _ , ≾ᵣ-reflexive (sym (·ᵣ-assoc _ _ _)) , Tl-⟨⟩ x
var-rename (⟨⟩-≤-ren {ρ = ρ₁} {ρ' = ρ₂} ρ₂≾ρ₁) (Tl-⟨⟩ x) =
  _ ·ᵣ ρ₂ , ·ᵣ-monoʳ-≾ᵣ ρ₂≾ρ₁ , Tl-⟨⟩ x
var-rename (cong-∷-ren r) Hd =
  uᵣ , ≾ᵣ-refl , Hd
var-rename (cong-∷-ren r) (Tl-∷ x) with var-rename r x
... | ρ' , ρ'≾ρ , y = ρ' , ρ'≾ρ , Tl-∷ y
var-rename (cong-⟨⟩-ren r) (Tl-⟨⟩ x) =
  var-rename r x .proj₁ ·ᵣ _ ,
  ·ᵣ-monoˡ-≾ᵣ (var-rename r x .proj₂ .proj₁) ,
  Tl-⟨⟩ (var-rename r x .proj₂ .proj₂)

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename r (var rel x) =
    var
    (≾ᵣ-trans (proj₁ (proj₂ (var-rename r x))) rel)
    (proj₂ (proj₂ (var-rename r x)))
  V-rename r (const c)   = const c
  V-rename r ⋆           = ⋆
  V-rename r (⦉ V , W ⦊)  = ⦉ V-rename r V , V-rename r W ⦊
  V-rename r (lam M)     = lam (C-rename (cong-ren r) M)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename r (return V)       = return (V-rename r V)
  C-rename r (M ; N)          = C-rename r M ; C-rename (cong-ren r) N
  C-rename r (V · W)          = V-rename r V · V-rename r W
  C-rename r (match V `in M)  = match V-rename r V `in C-rename (cong-ren r) M
  C-rename r (absurd V)       = absurd (V-rename r V)
  C-rename r (perform op V M) = perform op (V-rename r V) (C-rename (cong-ren r) M)
  C-rename r (delay τ M)      = delay τ (C-rename (cong-ren r) M)
  C-rename r (handle M `with H `in N) =
    handle C-rename r M
    `with (λ op ε'' Γ' → C-rename (cong-ren r) (H op ε'' Γ') )
    `in (C-rename (cong-ren r) N)
  C-rename {Γ' = Γ'} r (unbox {A} {C} {ρ} {ρ'} x rel M) =
    unbox {ρ = ρ} {ρ' = proj₁ (var-rename r x)}
      (proj₂ (proj₂ (var-rename r x)))
      (≾ᵣ-trans (proj₁ (proj₂ (var-rename r x))) rel)
      (C-rename (cong-ren r) M) 
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)
  C-rename r (coerce rel M) = coerce rel (C-rename r M)
