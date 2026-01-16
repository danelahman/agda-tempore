------------------------------------------------------------------
-- Parallel substitutions                                       --
--                                                              --
-- Note: These are raw (underlying) substitutions that are      --
-- further refined in Syntax.Substitutions to respect ctx-grade --
------------------------------------------------------------------

open import Syntax.Grades

module Syntax.Substitutions.Raw (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)

open import Util.Equality

-- Substitutions in terms

VSub : Ctx → Ctx → Set
VSub Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Ren (Γ₁ ++ᶜ Γ₂) Γ' × Γ₁ ⊢V⦂ A × ctx-grade Γ₂ ≾ᵣ ρ)
-- Identity substitution

id-sub : ∀ {Γ} → VSub Γ Γ
id-sub {Γ} {A = A} x =
  (proj₁ (var-split x)) ∷ A ,
  proj₁ (proj₂ (var-split x)) ,
  eq-ren (split-≡ ((proj₁ (proj₂ (proj₂ (var-split x)))))) ,
  var Hd ,
  ≾ᵣ-reflexive (proj₂ (proj₂ (proj₂ (var-split x))))

-- Composition of substitutions and renamings

_∘ʳˢ_ : ∀ {Γ Γ' Γ''} → VSub Γ' Γ'' → Ren Γ Γ' → VSub Γ Γ''
_∘ʳˢ_ s r x with var-rename r x
... | ρ' , rel , y with s y
... | Γ₁'' , Γ₂'' , r' , t , rel' = Γ₁'' , Γ₂'' , r' , t , ≾ᵣ-trans rel' rel

_∘ˢʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → VSub Γ Γ' → VSub Γ Γ''
_∘ˢʳ_ r s x with s x
... | Γ₁' , Γ₂' , r' , t , rel = Γ₁' , Γ₂' , r ∘ʳ r' , t , rel

-- Congruence substitutions

cong-∷-vsub : ∀ {Γ Γ' A} → VSub Γ Γ' → VSub (Γ ∷ A) (Γ' ∷ A)
cong-∷-vsub {Γ = Γ} {Γ' = Γ'} {A = A} s Hd =
  Γ' ∷ A , [] , id-ren , var Hd , ≾ᵣ-refl
cong-∷-vsub {Γ} {Γ'} {A} s (Tl-∷ x) with s x
... | Γ₁ , Γ₂ , r , t , rel =
  Γ₁ , Γ₂ ∷ A , cong-ren r , t , rel

cong-⟨⟩-vsub : ∀ {Γ Γ' ρ} → VSub Γ Γ' → VSub (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-vsub {ρ = ρ} s (Tl-⟨⟩ x) with s x
... | Γ₁ , Γ₂ , r , t , rel = Γ₁ , Γ₂ ⟨ ρ ⟩ , cong-ren r , t , ·ᵣ-monoˡ-≾ᵣ ρ rel

-- Congruence of substitutions

cong-vsub : ∀ {Γ Γ' Γ''} → VSub Γ Γ' → VSub (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-vsub {Γ'' = []} s        = s
cong-vsub {Γ'' = Γ'' ∷ A} s   = cong-∷-vsub (cong-vsub s)
cong-vsub {Γ'' = Γ'' ⟨ ρ ⟩} s = cong-⟨⟩-vsub (cong-vsub s)


-- TODO: complete
-- Identity laws
∘ʳˢ-identityʳ : ∀ {Γ Γ' A ρ}
              → (s : VSub Γ Γ')
              → (x : A ∈[ ρ ] Γ)
              → (s ∘ʳˢ id-ren) x ≡ s x
∘ʳˢ-identityʳ {Γ} {Γ'} {A} {ρ} s x =
  dcong₂ _,_ refl (dcong₂ _,_ refl (dcong₂ _,_ refl (cong₂ _,_ refl (≾ᵣ-irrelevant _ _))))

{-
∘ˢʳ-identityˡ : ∀ {Γ Γ' A ρ}
              → (s : VSub Γ Γ')
              → (x : A ∈[ ρ ] Γ)
              → (id-ren ∘ˢʳ s) x ≡ s x
∘ˢʳ-identityˡ {Γ} {Γ'} {A} {ρ} s x = dcong₂ _,_ refl (dcong₂ _,_ refl (cong₂ _,_ {!!} (dcong₂ _,_ refl refl)))
-}
