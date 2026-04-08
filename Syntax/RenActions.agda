{-# OPTIONS --allow-unsolved-metas #-} -- remove

------------------------------------------
-- Renaming actions on well-typed terms --
------------------------------------------

open import Syntax.Grades

module Syntax.RenActions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Language (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

var-ρ-subst : ∀ {Γ A ρ ρ'} → ρ ≡ ρ' → A ∈[ ρ ] Γ → A ∈[ ρ' ] Γ
var-ρ-subst refl x = x

var-rename : ∀ {Γ Γ' A ρ} → Ren Γ Γ' → A ∈[ ρ ] Γ → Σ[ ρ' ∈ R ] (ρ' ≾ᵣ ρ × A ∈[ ρ' ] Γ')
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
var-rename (⟨⟩-≤-ren {ρ = ρ₁} {ρ' = ρ₂} ρ₂≾ρ₁ pres) (Tl-⟨⟩ x) =
  _ ·ᵣ ρ₂ , ·ᵣ-monoʳ-≾ᵣ ρ₂≾ρ₁ , Tl-⟨⟩ x
var-rename (cong-∷-ren r) Hd =
  uᵣ , ≾ᵣ-refl , Hd
var-rename (cong-∷-ren r) (Tl-∷ x) with var-rename r x
... | ρ' , ρ'≾ρ , y = ρ' , ρ'≾ρ , Tl-∷ y
var-rename (cong-⟨⟩-ren r) (Tl-⟨⟩ x) =
  var-rename r x .proj₁ ·ᵣ _ ,
  ·ᵣ-monoˡ-≾ᵣ (var-rename r x .proj₂ .proj₁) ,
  Tl-⟨⟩ (var-rename r x .proj₂ .proj₂)

-- renaming preserves blocking behaviour

ren-pres-blck : ∀ {Γ Γ' A ρ ρ'}
              → (r : Ren Γ Γ')
              → (x : [ ρ ] A ∈[ ρ' ] Γ)
              → Beh-pres
                  (ctx-grade (proj₁ (proj₂ (var-split x))))
                  (ctx-grade (proj₁ (proj₂ (var-split (proj₂ (proj₂ (var-rename r x)))))))
                  Γ
ren-pres-blck r x = {!!}

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename r (var x) =
    var
    (var-ρ-subst
      (uᵣ-minimal (proj₁ (proj₂ (var-rename r x))))
      (proj₂ (proj₂ (var-rename r x))))
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
    `with (λ op τ'' → C-rename (cong-ren r) (H op τ'') )
    `in (C-rename (cong-ren r) N)
    
  C-rename {Γ' = Γ'} r (unbox {A} {C} {ρ} {ρ'} {v = v} rel neq eq M) with var-rename r v
  ... | ρ'' , ρ''≾ρ' , y =
    unbox {ρ = ρ} {ρ' = ρ''} {v = y}
      (ren-pres-blck {!!} {!!} {!!} {!!})
      {!!}
      (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split y))))))
      (C-rename (cong-ren r) M) 
  {-
  ... | Γ''' , r' , ρ'' , ex' , rel' =
    unbox {A = A} {Γ' = Γ'''} {ρ = ρ} {ρ' = ρ''}
      ex'
      (≾ᵣ-trans rel' rel)
      (V-rename r' V)
      (C-rename (cong-ren r) M)
  -}
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)

  -- sub-effecting
  C-rename r (coerce M relEff) = coerce (C-rename r M) relEff
