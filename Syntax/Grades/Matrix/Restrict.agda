------------------------------------------------------------------------
-- The equivariant sub-dioid of the elements with a property.         --
--                                                                    --
-- Let `P` be a property of the elements of an equivariant dioid that --
-- holds of `𝟘`, `𝟙` and `⊤` and is kept by `_⊕_`, `_⊗_`, the action  --
-- and orbit joins. Then the elements with a witness of `P` form an   --
-- equivariant dioid: the order is that of the dioid, the witness     --
-- being data it ignores, and every law is inherited.                 --
------------------------------------------------------------------------

open import Syntax.Grades.Indexed using (Names)
open import Syntax.Grades.Matrix.Dioid using (Dioid)
open import Syntax.Grades.Matrix.Nominal using (Equivariant)

module Syntax.Grades.Matrix.Restrict (𝒩 : Names) {S : Dioid} (Eq : Equivariant 𝒩 S) where

open import Data.List.Base using ([]; _∷_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)

open import Syntax.Grades.Matrix.Nominal 𝒩 using (Perm; Fixes; along)

open import Util.Equality

private
  module S = Dioid S
  module E = Equivariant Eq

record Closed (P : S.Carrier → Set) : Set where
  field
    P-𝟘     : P S.𝟘
    P-𝟙     : P S.𝟙
    P-⊤     : P S.⊤
    P-⊕     : ∀ {x y} → P x → P y → P (x S.⊕ y)
    P-⊗     : ∀ {x y} → P x → P y → P (x S.⊗ y)
    P-act   : ∀ {a b x} → P x → P (E.act a b x)
    P-orbit : ∀ {A x} → P x → P (E.⟨ x ⟩ A)

module _ {P : S.Carrier → Set} (C : Closed P) where

  open Closed C

  private
    T : Set
    T = Σ S.Carrier P

    actᵀ : _ → _ → T → T
    actᵀ a b (x , p) = E.act a b x , P-act p

    along-proj : ∀ π (x : T) → proj₁ (along actᵀ π x) ≡ E.actᴾ π (proj₁ x)
    along-proj []            x = refl
    along-proj ((a , b) ∷ π) x = cong (E.act a b) (along-proj π x)

  restricted : Dioid
  restricted = record
    { Carrier      = T
    ; _≤_          = λ x y → proj₁ x S.≤ proj₁ y
    ; 𝟘            = S.𝟘 , P-𝟘
    ; 𝟙            = S.𝟙 , P-𝟙
    ; ⊤            = S.⊤ , P-⊤
    ; _⊕_          = λ (x , p) (y , q) → x S.⊕ y , P-⊕ p q
    ; _⊗_          = λ (x , p) (y , q) → x S.⊗ y , P-⊗ p q
    ; ≤-refl       = S.≤-refl
    ; ≤-trans      = S.≤-trans
    ; ≤-irrelevant = S.≤-irrelevant
    ; _≤?_         = λ x y → proj₁ x S.≤? proj₁ y
    ; 𝟘-≤          = λ x → S.𝟘-≤ (proj₁ x)
    ; ≤-⊤          = λ x → S.≤-⊤ (proj₁ x)
    ; ⊕-ubˡ        = λ x y → S.⊕-ubˡ (proj₁ x) (proj₁ y)
    ; ⊕-ubʳ        = λ x y → S.⊕-ubʳ (proj₁ x) (proj₁ y)
    ; ⊕-lub        = S.⊕-lub
    ; ⊗-identityˡ  = λ x → S.⊗-identityˡ (proj₁ x)
    ; ⊗-identityʳ  = λ x → S.⊗-identityʳ (proj₁ x)
    ; ⊗-assoc      = λ x y z → S.⊗-assoc (proj₁ x) (proj₁ y) (proj₁ z)
    ; ⊗-mono       = S.⊗-mono
    ; ⊗-zeroˡ      = λ x → S.⊗-zeroˡ (proj₁ x)
    ; ⊗-zeroʳ      = λ x → S.⊗-zeroʳ (proj₁ x)
    ; ⊗-distribˡ   = λ x y z → S.⊗-distribˡ (proj₁ x) (proj₁ y) (proj₁ z)
    ; ⊗-distribʳ   = λ x y z → S.⊗-distribʳ (proj₁ x) (proj₁ y) (proj₁ z)
    }

  restricted-equivariant : Equivariant 𝒩 restricted
  restricted-equivariant = record
    { act       = actᵀ
    ; act-mono  = E.act-mono
    ; act-inv   = λ a b x → E.act-inv a b (proj₁ x)
    ; act-refl  = λ a x → E.act-refl a (proj₁ x)
    ; act-𝟘     = E.act-𝟘
    ; act-𝟙     = E.act-𝟙
    ; act-⊕     = λ a b x y → E.act-⊕ a b (proj₁ x) (proj₁ y)
    ; act-⊗     = λ a b x y → E.act-⊗ a b (proj₁ x) (proj₁ y)
    ; ⟨_⟩_      = λ (x , p) A → (E.⟨ x ⟩ A) , P-orbit p
    ; orbit-ub  = λ {A} {x} π fix →
        S.≤-trans (S.≤-reflexive (along-proj π x)) (E.orbit-ub π fix)
    ; orbit-lub = λ {A} {x} f →
        E.orbit-lub (λ π fix → S.≤-trans (S.≤-reflexive (sym (along-proj π x))) (f π fix))
    ; orbit-⊗ʳ  = λ {A} {x} f →
        E.orbit-⊗ʳ (λ π fix → S.≤-trans (S.⊗-mono (S.≤-reflexive (sym (along-proj π x))) S.≤-refl) (f π fix))
    ; orbit-⊗ˡ  = λ {A} {x} f →
        E.orbit-⊗ˡ (λ π fix → S.≤-trans (S.⊗-mono S.≤-refl (S.≤-reflexive (sym (along-proj π x)))) (f π fix))
    }
