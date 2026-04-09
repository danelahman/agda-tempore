{-# OPTIONS --allow-unsolved-metas #-} -- remove

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
              → (ρ ≾ᵣ ρ' ⊎ ρ' ≡ uᵣ)
              -----------------------------
              → ρ ≾ᵣ proj₁ (var-rename r x) ⊎ (proj₁ (var-rename r x) ≡ uᵣ)

ren-pres-blck id-ren _ (inj₁ rel) = inj₁ rel
ren-pres-blck id-ren x (inj₂ refl) = inj₂ refl
ren-pres-blck (r₂ ∘ʳ r₁) x rel =
  ren-pres-blck r₂ (var-rename r₁ x .proj₂ .proj₂) (ren-pres-blck r₁ x rel)
ren-pres-blck wk-ren _ rel =
  rel
ren-pres-blck (var-ren _) Hd rel =
  rel
ren-pres-blck (var-ren _) (Tl-∷ _) rel =
  rel
ren-pres-blck {ρ' = .(ρ' ·ᵣ uᵣ)} ⟨⟩-η-ren (Tl-⟨⟩ {ρ = .(uᵣ)} {ρ' = ρ'} x) (inj₁ ρ≾ρ'·u) =
  inj₁ (≾ᵣ-trans ρ≾ρ'·u (≾ᵣ-reflexive (·ᵣ-identityʳ ρ')))
ren-pres-blck {ρ' = ρ'} ⟨⟩-η-ren (Tl-⟨⟩ x) (inj₂ eq) =
  inj₂ (·ᵣ-zero-productˡ eq)
ren-pres-blck ⟨⟩-η⁻¹-ren Hd rel rewrite ·ᵣ-identityʳ uᵣ =
  rel
ren-pres-blck ⟨⟩-η⁻¹-ren (Tl-∷ x) (inj₁ ρ≾ρ') =
  inj₁ (≾ᵣ-trans ρ≾ρ' (≾ᵣ-reflexive (sym (·ᵣ-identityʳ _))))
ren-pres-blck ⟨⟩-η⁻¹-ren (Tl-∷ x) (inj₂ refl) =
  inj₂ (·ᵣ-identityʳ uᵣ)
ren-pres-blck ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) (inj₁ ρ≾ρ'·ρ₁) =
  inj₁ (≾ᵣ-trans ρ≾ρ'·ρ₁ (≾ᵣ-reflexive (sym (·ᵣ-identityʳ (_ ·ᵣ _)))))
ren-pres-blck ⟨⟩-η⁻¹-ren (Tl-⟨⟩ x) (inj₂ eq) =
  inj₂ (trans (·ᵣ-identityʳ (_ ·ᵣ _)) eq)
ren-pres-blck ⟨⟩-μ-ren (Tl-⟨⟩ x) (inj₁ rel) =
  inj₁ (≾ᵣ-trans rel (≾ᵣ-reflexive (sym (·ᵣ-assoc _ _ _))))
ren-pres-blck ⟨⟩-μ-ren (Tl-⟨⟩ x) (inj₂ eq) =
  inj₂ (trans (·ᵣ-assoc _ _ _) eq)
ren-pres-blck ⟨⟩-μ⁻¹-ren (Tl-⟨⟩ (Tl-⟨⟩ x)) (inj₁ rel) =
  inj₁ (≾ᵣ-trans rel (≾ᵣ-reflexive (·ᵣ-assoc _ _ _)) )
ren-pres-blck ⟨⟩-μ⁻¹-ren (Tl-⟨⟩ (Tl-⟨⟩ x)) (inj₂ refl) =
  inj₂ (sym (·ᵣ-assoc _ _ _))
ren-pres-blck (⟨⟩-≤-ren {ρ = ρ₁} {ρ' = ρ₂} ρ'≾ρ bprel) (Tl-⟨⟩ x) (inj₁ rel) =
  inj₁ (bprel x rel ρ'≾ρ)
ren-pres-blck (⟨⟩-≤-ren {ρ = ρ₁} {ρ' = ρ₂} ρ'≾ρ bprel) (Tl-⟨⟩ x) (inj₂ eq)
  rewrite ·ᵣ-zero-productˡ eq | ·ᵣ-zero-productʳ eq =
  inj₂ (trans (·ᵣ-identityˡ ρ₂) (uᵣ-minimal ρ'≾ρ))
ren-pres-blck (cong-∷-ren _) Hd rel =
  rel
ren-pres-blck (cong-∷-ren r) (Tl-∷ x) rel =
  ren-pres-blck r x rel
ren-pres-blck {Γ ⟨ ρ₁ ⟩} {Γ' ⟨ ρ₁ ⟩} {A} {ρ} (cong-⟨⟩-ren {ρ = ρ₁} r) (Tl-⟨⟩ {ρ = ρ₁} {ρ' = ρ'} x) (inj₁ rel)
  with ren-pres-blck r x (inj₁ {!!})
... | a = {!!}
ren-pres-blck {Γ ⟨ ρ₁ ⟩} {Γ' ⟨ ρ₁ ⟩} {A} {ρ} (cong-⟨⟩-ren {ρ = ρ₁} r) (Tl-⟨⟩ {ρ = ρ₁} {ρ' = ρ'} x) (inj₂ eq)
  rewrite ·ᵣ-zero-productˡ eq | ·ᵣ-zero-productʳ eq with ren-pres-blck r x (inj₂ refl)
... | inj₁ rel = inj₁ (≾ᵣ-trans rel (≾ᵣ-reflexive (sym (·ᵣ-identityʳ (var-rename r x .proj₁)))))
... | inj₂ eq rewrite eq = inj₂ (·ᵣ-identityʳ uᵣ)

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
  ... | ρ'' , ρ''≾ρ' , y rewrite (proj₂ (proj₂ (proj₂ (var-split v))))  =
    unbox {ρ = ρ} {ρ' = proj₁ (var-rename r v)} {v = proj₂ (proj₂ (var-rename r v))}
      {!!}
      {- (subst
        (λ ρ'' → ρ ≾ᵣ ρ'')
        (sym (proj₂ (proj₂ (proj₂ (var-split (proj₂ (proj₂ (var-rename r v))))))))
        (ren-pres-blck r v rel)) -}
      {!!}
      (sym (split-≡ (proj₁ (proj₂ (proj₂ (var-split (proj₂ (proj₂ (var-rename r v)))))))))
      (C-rename (cong-ren r) M) 
  C-rename r (box V M) = box (V-rename (cong-ren r) V) (C-rename (cong-ren r) M)

  -- sub-effecting
  C-rename r (coerce M relEff) = coerce (C-rename r M) relEff
