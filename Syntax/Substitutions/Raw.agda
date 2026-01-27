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

open import Syntax.Extensions.Raw (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Extensions (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)

open import Util.Equality

-- Substitutions in terms

VSub : Ctx → Ctx → Set
--VSub Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Ren (Γ₁ ++ᶜ Γ₂) Γ' × Γ₁ ⊢V⦂ A)
VSub Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] (Ren (Γ₁ ++ᶜ Γ₂) Γ' × Γ₁ ⊢V⦂ A × ctx-grade Γ₂ ≾ᵣ ρ)

-- Identity variable substitution

id-vsub : ∀ {Γ} → VSub Γ Γ
id-vsub {Γ} {A} x =
  proj₁ (var-split x) ∷ A ,
  proj₁ (proj₂ (var-split x)) ,
  eq-ren (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))) ,
--  var Hd
  var Hd ,
  ≾ᵣ-reflexive (proj₂ (proj₂ (proj₂ (var-split x))))

-- Composition of variable substitutions and renamings

--_ᵛ∘ʳˢ_ : ∀ {Γ Γ' Γ''} → VSub Γ' Γ'' → Ren Γ Γ' → VSub Γ Γ''
--_ᵛ∘ʳˢ_ vsub re x with var-rename re x
--... | ρ' , rel , y with vsub y
--... | Γ₁ , Γ₂ , re' , V , ex = Γ₁ , Γ₂ , re' , V , {!? ∘ʳᵉ ?!}

_ᵛ∘ˢʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → VSub Γ Γ' → VSub Γ Γ''
_ᵛ∘ˢʳ_ re vs x with vs x
... | Γ₁ , Γ₂ , re' , V = Γ₁ , Γ₂ , re ∘ʳ re' , V

-- -- Composition of variable substitutions and extensions

_ᵛ∘ᵉˢ_ : ∀ {Γ Γ' Γ''} → VSub Γ' Γ'' → VExt Γ Γ' → VSub Γ Γ''
_ᵛ∘ᵉˢ_ vs ve x with ve x
... | ρ , y with vs y
... | Γ₁ , Γ₂ , re , V , rel = Γ₁ , Γ₂ , re , V , ≾ᵣ-trans rel (ρ-≾ᵣ-substₗ (·ᵣ-identityˡ ρ) (c≾ᵣd⇒c·ᵣb≾ᵣd ρ uᵣ≾ᵣc))
--... | Γ₁ , Γ₂ , re , V = Γ₁ , Γ₂ , re , V

-- Congruence substitutions

cong-∷-vsub : ∀ {Γ Γ' A} → VSub Γ Γ' → VSub (Γ ∷ A) (Γ' ∷ A)
cong-∷-vsub {Γ' = Γ'} {A = A} vs Hd = 
--  Γ' ∷ A , [] , id-ren , var Hd
  Γ' ∷ A , [] , id-ren , var Hd , ≾ᵣ-refl
cong-∷-vsub {Γ} {Γ'} {A} vs (Tl-∷ x) with vs x
... | Γ₁ , Γ₂ , re , V  = Γ₁ , Γ₂ , wk-ctx-renᵣ refl ∘ʳ re , V
--... | Γ₁ , Γ₂ , re , V , rel  = Γ₁ , Γ₂ , wk-ctx-renᵣ refl ∘ʳ re , V , rel

cong-⟨⟩-vsub : ∀ {Γ Γ' ρ} → VSub Γ Γ' → VSub (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-vsub {ρ = ρ} vs (Tl-⟨⟩ x) with vs x
-- ... | Γ₁ , Γ₂ , re , V = Γ₁ , Γ₂ ⟨ ρ ⟩ , cong-⟨⟩-ren re , V
... | Γ₁ , Γ₂ , re , V , rel = Γ₁ , Γ₂ ⟨ ρ ⟩ , cong-⟨⟩-ren re , V , ·ᵣ-monoˡ-≾ᵣ ρ rel

-- Congruence of substitutions

cong-vsub : ∀ {Γ Γ' Γ''} → VSub Γ Γ' → VSub (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-vsub {Γ'' = []} vs        = vs
cong-vsub {Γ'' = Γ'' ∷ A} vs   = cong-∷-vsub (cong-vsub vs)
cong-vsub {Γ'' = Γ'' ⟨ ρ ⟩} vs = cong-⟨⟩-vsub (cong-vsub vs)

-- -- TODO: complete
-- -- Identity laws
-- ᵛ∘ʳˢ-identityʳ : ∀ {Γ Γ' A ρ}
--               → (s : VSub Γ Γ')
--               → (x : A ∈[ ρ ] Γ)
--               → (s ᵛ∘ʳˢ id-ren) x ≡ s x
-- ᵛ∘ʳˢ-identityʳ {Γ} {Γ'} {A} {ρ} s x =
--   dcong₂ _,_ refl (dcong₂ _,_ refl (dcong₂ _,_ refl (cong₂ _,_ refl (≾ᵣ-irrelevant _ _))))

-- {-
-- ᵛ∘ˢʳ-identityˡ : ∀ {Γ Γ' A ρ}
--               → (s : VSub Γ Γ')
--               → (x : A ∈[ ρ ] Γ)
--               → (_ᵛ∘ˢʳ_ id-ren s) x ≡ s x
-- -}

-- -- Variable substitution implies renaming

ren⇒vsub : ∀ {Γ Γ'} → Ren Γ Γ' → VSub Γ Γ'
ren⇒vsub {Γ} {Γ'} r {A} {ρ} x =
  proj₁ (var-split x) ∷ A ,
  proj₁ (proj₂ (var-split x)) ,
  r ∘ʳ eq-ren (split-≡ (proj₁ (proj₂ (proj₂ (var-split x))))) ,
  var Hd ,
  ≾ᵣ-reflexive (proj₂ (proj₂ (proj₂ (var-split x))))


