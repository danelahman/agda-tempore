{-# OPTIONS --allow-unsolved-metas #-} -- remove

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
open import Syntax.Language (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.Types (Grades)

open import Util.Equality
open import Util.Operations (Grades)

-- Substituting a value for a variable in context

⟨_,_⟩[_↦_]var : ∀ {Γ A B ρ ρ'}
          → B ∈[ ρ' ] Γ
          → ρ' ≾ᵣ uᵣ
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B
          
⟨ Hd , p ⟩[ Hd ↦ W ]var =
  W
⟨ Hd , p ⟩[ Tl-∷ x ↦ W ]var =
  var ≾ᵣ-refl Hd
⟨ Tl-∷ y , rel ⟩[ Hd ↦ W ]var =
  var rel y
⟨ Tl-∷ y , rel ⟩[ Tl-∷ x ↦ W ]var =
  V-rename wk-ren ⟨ y , rel ⟩[ x ↦ W ]var
⟨ Tl-⟨⟩ y , rel ⟩[ Tl-⟨⟩ x ↦ W ]var =
  V-rename (⟨⟩-≤-ren (≾ᵣ-zero-productʳ rel) ∘ʳ ⟨⟩-η⁻¹-ren) ⟨ y , ≾ᵣ-zero-productˡ rel ⟩[ x ↦ W ]var

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B ρ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ ρ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  var rel y   [ x ↦ W ]v = ⟨ y , rel ⟩[ x ↦ W ]var
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

  return rel V    [ x ↦ W ]c = return rel (V [ x ↦ W ]v)
  (M ; N)         [ x ↦ W ]c = (M [ x ↦ W ]c) ; (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂)       [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  (match V `in N) [ x ↦ W ]c = match V [ x ↦ W ]v `in (N [ Tl-∷ (Tl-∷ x) ↦ W ]c)
  absurd V        [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M  [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  delay τ M       [ x ↦ W ]c = delay τ (M [ Tl-⟨⟩ x ↦ W ]c)
  handle_`with_`in {B = B} M H N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with (λ op ε'' Γ' →
            C-rename
              (eq-ren (
                begin
                  proj₁ (var-split (var-ρ-++ᶜ {Γ' = Γ'} x)) ++ᶜ
                   proj₁ (proj₂ (var-split (Tl-∷ (Tl-∷ (var-ρ-++ᶜ {Γ' = Γ'} x)))))

                ≡⟨ cong₂ _∷_ (cong₂ _∷_ (cong₂ _++ᶜ_ (sym (split-var-eqₗ {Γ' = Γ'} x)) refl ) refl ) refl ⟩

                  proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split (var-ρ-++ᶜ {Γ' = Γ'} x))) ∷ _ ∷ _

                ≡⟨ cong₂ _∷_ (cong₂ _∷_ (cong₂ _++ᶜ_ refl (sym (split-var-eqᵣ {Γ' = Γ'} x))) refl) refl ⟩

                  proj₁ (var-split x) ++ᶜ (proj₁ (proj₂ (var-split x)) ++ᶜ Γ' ∷ _ ∷ _)

                ≡⟨ sym (++ᶜ-assoc (proj₁ (var-split x)) (proj₁ (proj₂ (var-split x))) ((Γ' ∷ _) ∷ _)) ⟩
                    
                  proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ++ᶜ ((Γ' ∷ _) ∷ _)                    
                ∎
              ))
              ((H op ε'' Γ') [ Tl-∷ (Tl-∷ (var-ρ-++ᶜ x)) ↦ V-rename (eq-ren (split-var-eqₗ {Γ' = Γ'} x)) W ]c))
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c (unbox {A = B} {ρ = ρ₁} {ρ' = ρ₂} y rel M) x W with var-in-split (proj₁ (proj₂ (proj₂ (var-split x)))) y
  ... | inj₁ (.(uᵣ) , Hd , eq , eq') =
    unbox
      (var-ρ-++ᶜ {Γ' = proj₁ (proj₂ (var-split x))} (proj₁ (proj₂ (proj₂ (grad-typ⇒var W)))))
      (≾ᵣ-trans
        (≾ᵣ-trans
          (·ᵣ-monoˡ-≾ᵣ (proj₁ (proj₂ (grad-typ⇒var W))))
          (≾ᵣ-reflexive
            (trans
              (·ᵣ-identityˡ (ctx-grade (proj₁ (proj₂ (var-split x)))))
              (cong ctx-grade (trans (sym (++ᶜ-identityˡ {Γ = proj₁ (proj₂ (var-split x))})) (sym eq'))))))
        (≾ᵣ-trans (≾ᵣ-reflexive (proj₂ (proj₂ (proj₂ (var-split y))))) rel))
      (M [ Tl-∷ x ↦ W ]c)
  ... | inj₁ (ρ' , Tl-∷ z , eq , eq') =
    unbox {ρ = ρ₁} {ρ' = ρ₂}
      (var-ρ-subst
      (begin
        ρ' ·ᵣ ctx-grade (proj₁ (proj₂ (var-split x)))
      ≡⟨ cong
         (_·ᵣ ctx-grade (proj₁ (proj₂ (var-split x))))
         (sym (proj₂ (proj₂ (proj₂ (var-split (Tl-∷ {B = [ ρ₁ ] B} z)))))) ⟩
        ctx-grade (proj₁ (proj₂ (var-split (Tl-∷ {B = [ ρ₁ ] B} z)))) ·ᵣ ctx-grade (proj₂ (var-split x) .proj₁)
      ≡⟨ sym (ctx-grade-++ᶜ ((proj₁ (proj₂ (var-split (Tl-∷ z))))) (proj₂ (var-split x) .proj₁)) ⟩
        ctx-grade (proj₁ (proj₂ (var-split (Tl-∷ z))) ++ᶜ proj₂ (var-split x) .proj₁)
      ≡⟨ cong ctx-grade (sym eq') ⟩
        ctx-grade (proj₁ (proj₂ (var-split y)))
      ≡⟨ proj₂ (proj₂ (proj₂ (var-split y))) ⟩
        ρ₂
      ∎)
        (var-ρ-++ᶜ z))
      rel
      (M [ Tl-∷ x ↦ W ]c)
  ... | inj₂ (z , _ , _) =
    unbox
      (∈-ctx-extensionˡ (proj₁ (var-split x)) (proj₁ (proj₂ (var-split x))) z)
      rel
      (M [ Tl-∷ x ↦ W ]c)
  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce rel M [ x ↦ W ]c = coerce rel (M [ x ↦ W ]c)
