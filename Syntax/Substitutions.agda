-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Function using (case_of_)

open import Relation.Nullary

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Substitutions (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts   S
open import Syntax.Language   S
open import Syntax.RenActions S
open import Syntax.Renamings  S
open import Syntax.Types      S

-- Substituting a value for a variable in context

⟨_,_⟩[_↦_]var : ∀ {Γ A B ρ ρ'}
          → B ∈[ ρ' ] Γ
          → (¬ Eternal B → ρ' ≾ᵣ uᵣ)
          → (x : A ∈[ ρ ] Γ)
          → split-l x ⊢V⦂ A
          -------------------------------
          → split-l x ++ᶜ split-r x ⊢V⦂ B
          
⟨ Hd , _ ⟩[ Hd ↦ W ]var =
  W
⟨ Hd , f ⟩[ Tl-∷ _ ↦ _ ]var =
  var f Hd
⟨ Tl-∷ y , f ⟩[ Hd ↦ _ ]var =
  var f y
⟨ Tl-∷ y , f ⟩[ Tl-∷ x ↦ W ]var =
  V-rename wk-ren ⟨ y , f ⟩[ x ↦ W ]var
⟨_,_⟩[_↦_]var {B = B} (Tl-⟨⟩ y) f (Tl-⟨⟩ x) W with eternal? B
⟨ Tl-⟨⟩ y , f ⟩[ Tl-⟨⟩ x ↦ W ]var | yes p = -- TODO: check this case (if eternal, we can weaken the grade of Γ)
  eternal-val-ext p ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f (λ z₁ → z p))) ⟩[ x ↦ W ]var
⟨ Tl-⟨⟩ y , f ⟩[ Tl-⟨⟩ x ↦ W ]var | no ¬p = 
  V-rename (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬p)) ∘ʳ ⟨⟩-η⁻¹-ren) ⟨ y , (λ z → ≾ᵣ-zero-productˡ (f z)) ⟩[ x ↦ W ]var

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B ρ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ ρ ] Γ)
          → split-l x ⊢V⦂ A
          -------------------------------
          → split-l x ++ᶜ split-r x ⊢V⦂ B

  var f y     [ x ↦ W ]v = ⟨ y , f ⟩[ x ↦ W ]var
  const c     [ x ↦ W ]v = const c
  ⦉ V₁ , V₂ ⦊  [ x ↦ W ]v = ⦉ V₁ [ x ↦ W ]v , V₂ [ x ↦ W ]v ⦊
  ⋆           [ x ↦ W ]v = ⋆
  lam M       [ x ↦ W ]v = lam (M [ Tl-∷ x ↦ W ]c)

  _[_↦_]c : ∀ {Γ A C ρ}
          → Γ ⊢C⦂ C
          → (x : A ∈[ ρ ] Γ)
          → split-l x ⊢V⦂ A
          -------------------------------
          → split-l x ++ᶜ split-r x ⊢C⦂ C

  return V        [ x ↦ W ]c = return (V [ x ↦ W ]v)
  (M ⨟ N)         [ x ↦ W ]c = (M [ x ↦ W ]c) ⨟ (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂)       [ x ↦ W ]c = (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  (match V `in N) [ x ↦ W ]c = match V [ x ↦ W ]v `in (N [ Tl-∷ (Tl-∷ x) ↦ W ]c)
  absurd V        [ x ↦ W ]c = absurd (V [ x ↦ W ]v)
  perform op V M  [ x ↦ W ]c = perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  delay τ M       [ x ↦ W ]c = delay τ (M [ Tl-⟨⟩ x ↦ W ]c)
  handle_`with_`in {B = B} M H N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with H
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  -- For the value-based unboxing we first recover the underlying variable `y`
  -- (and grade bound `rel`) being unboxed via `unbox⇒var`, and then proceed
  -- exactly as in the variable case, rebuilding a value-based unboxing from the
  -- (possibly substituted) variable via the `unbox-var` smart constructor.
  _[_↦_]c (unbox {A = B} {ρ = ρ₁} w V M) x W with unbox⇒var w V
  ... | ρ₂ , y , rel with var-in-split (split-pf x) y
  ...   | inj₁ (.(uᵣ) , Hd , eq , eq') =
    unbox-var
      (var-ρ-++ᶜ (proj₁ (proj₂ (grad-typ⇒var W))))
      (≾ᵣ-trans
        (≾ᵣ-trans
          (·ᵣ-monoˡ-≾ᵣ ((proj₁ (proj₂ (proj₂ (grad-typ⇒var W)))) λ ()))
          (≾ᵣ-reflexive
            (trans
              (·ᵣ-identityˡ (ctx-grade (split-r x)))
              (cong ctx-grade (trans (sym (++ᶜ-identityˡ {Γ = split-r x})) (sym eq'))))))
        (≾ᵣ-trans (≾ᵣ-reflexive (split-grade-≡ y)) rel))
      (M [ Tl-∷ x ↦ W ]c)
  ...   | inj₁ (ρ' , Tl-∷ z , eq , eq') =
    unbox-var {ρ = ρ₁} {ρ' = ρ₂}
      (var-ρ-subst
      (begin
        ρ' ·ᵣ ctx-grade (split-r x)
      ≡⟨ cong
         (_·ᵣ ctx-grade (split-r x))
         (sym (split-grade-≡ (Tl-∷ {B = [ ρ₁ ] B} z))) ⟩
        ctx-grade (split-r (Tl-∷ {B = [ ρ₁ ] B} z)) ·ᵣ ctx-grade (split-r x)
      ≡⟨ sym (ctx-grade-++ᶜ (split-r (Tl-∷ z)) (split-r x)) ⟩
        ctx-grade (split-r (Tl-∷ z) ++ᶜ split-r x)
      ≡⟨ cong ctx-grade (sym eq') ⟩
        ctx-grade (split-r y)
      ≡⟨ split-grade-≡ y ⟩
        ρ₂
      ∎)
        (var-ρ-++ᶜ z))
      rel
      (M [ Tl-∷ x ↦ W ]c)
  ...   | inj₂ (z , _ , _) =
    unbox-var
      (∈-ctx-extensionˡ (split-l x) (split-r x) z)
      rel
      (M [ Tl-∷ x ↦ W ]c)
  box V N      [ x ↦ W ]c = box (V [ Tl-⟨⟩ x ↦ W ]v) (N [ Tl-∷ x ↦ W ]c)
  coerce rel M [ x ↦ W ]c = coerce rel (M [ x ↦ W ]c)
