----------------------------
-- Parallel substitutions --
----------------------------

open import Syntax.Grades

module Syntax.Substitutions.ParallelSubstitutions (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)

open import Util.Equality

-- Substitutions in terms

Sub : Ctx → Ctx → Set
Sub Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Ren (Γ₁ ++ᶜ Γ₂) Γ' × Γ₁ ⊢V⦂ A × ctx-grade Γ₂ ≾ᵣ ρ)
-- Identity substitution

id-sub : ∀ {Γ} → Sub Γ Γ
id-sub {Γ} {A = A} x =
  (proj₁ (var-split x)) ∷ A ,
  proj₁ (proj₂ (var-split x)) ,
  eq-ren (split-≡ ((proj₁ (proj₂ (proj₂ (var-split x)))))) ,
  var Hd ,
  ≾ᵣ-reflexive (proj₂ (proj₂ (proj₂ (var-split x))))

-- Substitutions and renamings compositions

_∘ʳˢ_ : ∀ {Γ Γ' Γ''} → Sub Γ' Γ'' → Ren Γ Γ' → Sub Γ Γ''
_∘ʳˢ_ s r x with var-rename r x
... | ρ' , rel , y with s y
... | Γ₁'' , Γ₂'' , r' , t , rel' = Γ₁'' , Γ₂'' , r' , t , ≾ᵣ-trans rel' rel

_∘ˢʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Sub Γ Γ' → Ren Γ Γ''
_∘ˢʳ_ r s = r ∘ʳ (proj₁ (proj₂ (proj₂ (s _))) ∘ʳ {!!})

{-
_∘ˢʳ_ {Γ} r s = 
  ren
    (≾ᵣ-trans
      (ctx-grade-≾ r)
      (≾ᵣ-trans
        (ctx-grade-≾ (proj₁ (proj₂ (proj₂ (s _)))))
        (≾ᵣ-trans
          {!!}
          {!!})))
    (var-rename r ∘ᵛʳ {!!})
-}
