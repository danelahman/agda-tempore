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
⟨ Tl-∷ y , refl ⟩[ Tl-∷ x ↦ W ]var = V-rename wk-ren ⟨ y , refl ⟩[ x ↦ W ]var
⟨ Tl-⟨⟩ y , p ⟩[ Tl-⟨⟩ x ↦ W ]var rewrite ·ᵣ-zero-productˡ p | ·ᵣ-zero-productʳ p =
  V-rename ⟨⟩-η⁻¹-ren ⟨ y , refl ⟩[ x ↦ W ]var

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

  return V rel    [ x ↦ W ]c = return (V [ x ↦ W ]v) rel
  (M ; N)         [ x ↦ W ]c = (M [ x ↦ W ]c) ; (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂)       [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  (match V `in N) [ x ↦ W ]c = match V [ x ↦ W ]v `in (N [ Tl-∷ (Tl-∷ x) ↦ W ]c)
  absurd V        [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M  [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  delay τ M       [ x ↦ W ]c = delay τ (M [ Tl-⟨⟩ x ↦ W ]c)
  handle M `with H `in N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with  (λ op ε Γ'' → (H op ε Γ'') [ {!!} ↦ {!!} ]c)
      -- [  Tl-∷ (Tl-∷ x)  ↦ W ]c)
    `in    (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c (unbox {A = B} {ρ = ρ₁} {ρ' = ρ₂} y rel M) x W with var-in-split (proj₁ (proj₂ (proj₂ (var-split x)))) y
  ... | inj₁ (.(uᵣ) , Hd , _ , eq') =
    unbox
      (var-ρ-subst
        (begin
          uᵣ ·ᵣ ctx-grade (proj₂ (var-split x) .proj₁)
        ≡⟨ sym (ctx-grade-++ᶜ [] (proj₁ (proj₂ (var-split x)))) ⟩
          ctx-grade
           ([] ++ᶜ proj₂ (var-split x) .proj₁)
        ≡⟨ cong ctx-grade (sym eq') ⟩
          ctx-grade (proj₁ (proj₂ (var-split y)))
        ≡⟨ proj₂ (proj₂ (proj₂ (var-split y))) ⟩
          ρ₂
        ∎)
        (var-ρ-++ᶜ (proj₁ (grad-typ⇒var W))))
      rel
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
  coerce M rel [ x ↦ W ]c = coerce (M [ x ↦ W ]c) rel
