-----------------------------------------------------
-- Substitution of well-typed values for variables --
-----------------------------------------------------

module Syntax.Substitutions where

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings
open import Syntax.Types

open import Util.Equality
open import Util.Time

-- Deciding whether a variable is in the context after time travelling

---- When the variable is in the resulting context

var-in-ctx-after-ᶜ : ∀ {Γ A τ τ'}
                   → (x : A ∈[ τ ] Γ)
                   → τ' ≤ τ
                   → Σ[ y ∈ A ∈[ τ ∸ τ' ] Γ -ᶜ τ' ]
                       (  proj₁ (var-split y) ≡ proj₁ (var-split x)
                        × proj₁ (proj₂ (var-split y)) ≡ proj₁ (proj₂ (var-split x)) -ᶜ τ')
                          
var-in-ctx-after-ᶜ {Γ} {A} {τ} {zero} x p =
  x , refl , refl
var-in-ctx-after-ᶜ {Γ ∷ B} {A} {τ} {suc τ'} (Tl-∷ x) p =
  var-in-ctx-after-ᶜ x p
var-in-ctx-after-ᶜ {Γ ⟨ τ'' ⟩} {A} {.(τ'' + _)} {suc τ'} (Tl-⟨⟩ {τ' = τ'''} x) p with suc τ' ≤? τ''
... | yes q rewrite trans                                              -- : τ'' + τ''' ∸ suc τ' ≡ (τ'' ∸ suc τ') + τ'''
            (cong (_∸ suc τ') (+-comm τ'' τ'''))
            (trans
              (+-∸-assoc τ''' q)
              (+-comm τ''' (τ'' ∸ suc τ'))) =
  Tl-⟨⟩ x , refl , refl
... | no ¬q rewrite trans                                              -- : τ'' + τ''' ∸ suc τ' ≡ τ''' ∸ (suc τ' ∸ τ'')
            (cong (_∸ suc τ') (+-comm τ'' τ'''))
            (¬k≤m⇒k∸m≤n⇒n+m∸k≤n∸k∸m {τ'''} {τ''} {suc τ'} ¬q
              (≤-trans (∸-monoˡ-≤ τ'' p) (≤-reflexive (m+n∸m≡n τ'' τ''')))) =
  var-in-ctx-after-ᶜ {Γ} {τ' = suc τ' ∸ τ''} x
    (≤-trans
      (∸-monoˡ-≤ τ'' p)
      (≤-reflexive (m+n∸m≡n τ'' τ''')))

---- When the variable is not in the resulting context

var-not-in-ctx-after-ᶜ : ∀ {Γ A τ τ'}
                       → (x : A ∈[ τ ] Γ)
                       → τ' > τ
                       → Γ -ᶜ τ' ≡ proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) -ᶜ τ'

var-not-in-ctx-after-ᶜ {Γ ∷ B} {.B} {.0} {suc τ'} Hd p =
  refl
var-not-in-ctx-after-ᶜ {Γ ∷ B} {A} {τ} {suc τ'} (Tl-∷ x) p =
  var-not-in-ctx-after-ᶜ {Γ} {τ' = suc τ'} x p
var-not-in-ctx-after-ᶜ {Γ ⟨ τ'' ⟩} {A} {.(τ'' + _)} {suc τ'} (Tl-⟨⟩ {τ' = τ'''} x) (s≤s p) with suc τ' ≤? τ''
... | yes q = 
  ⊥-elim (sucn≤m⇒m+k≤n-contradiction q p)
... | no ¬q =
  var-not-in-ctx-after-ᶜ {Γ} {τ' = suc τ' ∸ τ''} x
    (≤-trans
      (≤-trans
        (+-monoʳ-≤ 1 (≤-reflexive (sym (m+n∸m≡n τ'' τ'''))))
        (≤-reflexive (sym (+-∸-assoc 1 {τ'' + τ'''} {τ''} (m≤n⇒m≤n+o τ''' ≤-refl)))))
      (∸-monoˡ-≤ τ'' (+-monoʳ-≤ 1 p)))

-- Substituting a value for a variable in context

_[_↦_]var : ∀ {Γ A B τ τ'}
          → B ∈[ τ' ] Γ
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B
 
Hd [ Hd ↦ W ]var = W
Hd [ Tl-∷ x ↦ W ]var with var-split x
... | Γ₁ , Γ₂ , p , q = var Hd
Tl-∷ y [ Hd ↦ W ]var = var y
Tl-∷ y [ Tl-∷ x ↦ W ]var with var-split x | inspect var-split x
... | ._ , ._ , ._ , ._ | [| refl |] =
  V-rename wk-ren (y [ x ↦ W ]var)
Tl-⟨⟩ y [ Tl-⟨⟩ x ↦ W ]var with var-split x | inspect var-split x
... | ._ , ._ , ._ , ._ | [| refl |] =
  V-rename wk-⟨⟩-ren (y [ x ↦ W ]var)

-- Substituting a value for a variable in a well-typed term

mutual

  _[_↦_]v : ∀ {Γ A B τ}
          → Γ ⊢V⦂ B
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢V⦂ B

  var y      [ x ↦ W ]v = y [ x ↦ W ]var
  const c    [ x ↦ W ]v = const c
  ⦉ V₁ , V₂ ⦊ [ x ↦ W ]v = ⦉ V₁ [ x ↦ W ]v , V₂ [ x ↦ W ]v ⦊
  ⋆          [ x ↦ W ]v = ⋆
  lam M      [ x ↦ W ]v = lam (M [ Tl-∷ x ↦ W ]c)

  _[_↦_]c : ∀ {Γ A C τ}
          → Γ ⊢C⦂ C
          → (x : A ∈[ τ ] Γ)
          → proj₁ (var-split x) ⊢V⦂ A
          -----------------------------------------------------------
          → proj₁ (var-split x) ++ᶜ proj₁ (proj₂ (var-split x)) ⊢C⦂ C

  return V [ x ↦ W ]c =
    return (V [ x ↦ W ]v)
  (M ; N) [ x ↦ W ]c =
    (M [ x ↦ W ]c) ; (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  (V₁ · V₂) [ x ↦ W ]c =
    (V₁ [ x ↦ W ]v) · (V₂ [ x ↦ W ]v)
  (match V `in M) [ x ↦ W ]c =
    match V [ x ↦ W ]v `in (M [ Tl-∷ (Tl-∷ x) ↦ W ]c)
  absurd V [ x ↦ W ]c =
    absurd (V [ x ↦ W ]v)
  perform op V M [ x ↦ W ]c =
    perform op (V [ x ↦ W ]v) (M [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  delay τ M [ x ↦ W ]c =
    delay τ (M [ Tl-⟨⟩ x ↦ W ]c)
  handle M `with H `in N [ x ↦ W ]c =
    handle M [ x ↦ W ]c
    `with (λ op τ'' → (H op τ'') [ Tl-∷ (Tl-∷ x) ↦ W ]c)
    `in (N [ Tl-∷ (Tl-⟨⟩ x) ↦ W ]c)
  _[_↦_]c {τ = τ} (unbox {τ = τ'} s V M) x W with τ' ≤? τ
  _[_↦_]c {τ = τ} (unbox {τ = τ'} s V M) x W | yes p with var-in-ctx-after-ᶜ x p
  ... | y , q , r =
    unbox
      (≤-trans s (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
      (V-rename
        (   eq-ren
              (++ᶜ-ᶜ {proj₁ (var-split x)} {proj₁ (proj₂ (var-split x))} {τ'}
                (≤-trans p (≤-reflexive (sym (proj₂ (proj₂ (proj₂ (var-split x))))))))
         ∘ʳ eq-ren (cong₂ _++ᶜ_ q r))
        (V [ y ↦ V-rename (eq-ren (sym q)) W ]v))
      (M [ Tl-∷ x ↦ W ]c)
  _[_↦_]c {τ = τ} (unbox {τ = τ'} s V M) x W | no ¬p =
    unbox
      (≤-trans s (≤-reflexive (split-pres-ctx-time (proj₁ (proj₂ (proj₂ (var-split x)))))))
      (V-rename (eq-ren (var-not-in-ctx-after-ᶜ x (≰⇒> ¬p))) V)
      (M [ Tl-∷ x ↦ W ]c)
  box V M [ x ↦ W ]c  = 
    box (V [ Tl-⟨⟩ x ↦ W ]v) (M [ Tl-∷ x ↦ W ]c)
