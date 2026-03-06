-- {-# OPTIONS --allow-unsolved-metas #-} -- (remove)

--------------------------------------------------------------
-- Context renamings                                        --
--                                                          --
-- Note: These are raw (underlying) renamings that are      --
-- further refined in Syntax.Renamings to respect ctx-grade --
--------------------------------------------------------------

open import Syntax.Grades

module Syntax.Renamings (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Empty
open import Data.Product
open import Data.Sum

open import Relation.Nullary

open import Syntax.Contexts (Grades)
open import Syntax.Types (Grades)

open import Util.Equality

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] ) 

-- Variable renamings (as the smallest relation closed under
-- identities, composition, congruences, ordinary variable 
-- renamings, and strong monoidal functor sturcture for ⟨_⟩)

data Ren : Ctx → Ctx → Set where
  -- identity renaming
  id-ren      : ∀ {Γ} → Ren Γ Γ
  -- composition of renamings
  _∘ʳ_        : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
  -- weakening renaming
  wk-ren      : ∀ {Γ A} → Ren Γ (Γ ∷ A)
  -- variable renaming (corresponds to contraction)
  var-ren     : ∀ {Γ A} → A ∈[ uᵣ ] Γ → Ren (Γ ∷ A) Γ                -- TODO: in non-expring setting this was for general ρ
  -- strong monoidal functor renamings for ⟨_⟩ modality
  ⟨⟩-η-ren    : ∀ {Γ} → Ren (Γ ⟨ uᵣ ⟩) Γ
  ⟨⟩-η⁻¹-ren  : ∀ {Γ} → Ren Γ (Γ ⟨ uᵣ ⟩)
  ⟨⟩-μ-ren    : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
  ⟨⟩-μ⁻¹-ren  : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ'  ⟩)
  -- monotonicity renaming for 
  ⟨⟩-≤-ren    : ∀ {Γ ρ ρ'} → ρ' ≾ᵣ ρ → Ren (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
  -- congruence renamings ⟨_⟩ modality
  cong-∷-ren  : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
  cong-⟨⟩-ren : ∀ {Γ Γ' ρ} → Ren Γ Γ' → Ren (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)

infixr 20 _∘ʳ_

-- TODO: definitions of natural concrete renamings (see original development)

-- ...

-- "Time-travelling" operation on renamings

_-ʳ_,_ : ∀ {Γ Γ' Γ''}
       → Ren Γ Γ'
       → (ρ : R)
       → Γ -ᶜ ρ ≈ Γ''
       → Σ[ Γ''' ∈ Ctx ] Γ' -ᶜ ρ ≈ Γ''' × Ren Γ'' Γ'''

r -ʳ ρ , p with ρ ≡ᵣ? uᵣ
r -ʳ ρ , p | yes refl rewrite -ᶜ-u p =
  _ , -ᶜ-uᵣ refl , r
id-ren -ʳ ρ , p | no ρ≢ᵣuᵣ =
  _ , p , id-ren
(r₂ ∘ʳ r₁) -ʳ ρ , p | no ρ≢ᵣuᵣ with r₁ -ʳ ρ , p
... | Γ''' , q , r' with r₂ -ʳ ρ , q
... | Γ'''' , s , r'' =
  Γ'''' , s , r'' ∘ʳ r'
wk-ren -ʳ ρ , p | no ρ≢ᵣuᵣ =
  _ , -ᶜ-∷ ρ≢ᵣuᵣ p , id-ren
(var-ren x -ʳ ρ , -ᶜ-uᵣ p) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ p)
(var-ren x -ʳ ρ , -ᶜ-∷ p q) | no ρ≢ᵣuᵣ =
  _ , q , id-ren
(⟨⟩-η-ren -ʳ ρ , -ᶜ-uᵣ p) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ p)
(⟨⟩-η-ren -ʳ ρ , -ᶜ-⟨⟩-lt p q) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ (·ᵣ-zero-productʳ (sym q)))
(⟨⟩-η-ren -ʳ ρ , -ᶜ-⟨⟩-gt {ρ'' = ρ''} p q s t) | no ρ≢ᵣuᵣ rewrite ·ᵣ-identityʳ ρ'' | s =
  _ , t , id-ren
⟨⟩-η⁻¹-ren -ʳ ρ , p | no ρ≢ᵣuᵣ =
  _ , -ᶜ-⟨⟩-gt ρ≢ᵣuᵣ (λ { (ρ''' , q) → ⊥-elim (ρ≢ᵣuᵣ (·ᵣ-zero-productʳ (sym q))) }) (sym (·ᵣ-identityʳ ρ)) p , id-ren
(⟨⟩-μ-ren -ʳ ρ , -ᶜ-uᵣ p) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ p)
(⟨⟩-μ-ren -ʳ ρ , -ᶜ-⟨⟩-lt p q) | no ρ≢ᵣuᵣ with ·ᵣ-equidivisible q
... | inj₁ (ρ'' , s , t , u) rewrite sym t =
  _ , -ᶜ-⟨⟩-lt ρ≢ᵣuᵣ u , ⟨⟩-μ-ren
... | inj₂ (inj₁ (refl , refl)) =
  _ , -ᶜ-⟨⟩-lt ρ≢ᵣuᵣ (sym (·ᵣ-identityˡ ρ)) , ⟨⟩-η⁻¹-ren
... | inj₂ (inj₂ (ρ'' , s , t , u)) =
  _ ,
  -ᶜ-⟨⟩-gt
    ρ≢ᵣuᵣ
    (λ { (ρ'' , v) → s (·ᵣ-zero-productʳ (·ᵣ-cancellativeˡ
      (sym (trans (·ᵣ-identityˡ _) (trans (trans v (cong (ρ'' ·ᵣ_) (sym u))) (sym (·ᵣ-assoc _ _ _))))))) })
    (sym u) (-ᶜ-⟨⟩-lt s t) ,
  id-ren
(⟨⟩-μ-ren {ρ = ρ'} {ρ' = ρ''} -ʳ ρ , -ᶜ-⟨⟩-gt {ρ'' = ρ'''} p q s t) | no ρ≢ᵣuᵣ with ρ''' ≡ᵣ? uᵣ
... | yes refl =
  ⊥-elim (q (uᵣ , trans (trans (sym (·ᵣ-identityˡ _)) (sym s)) (sym (·ᵣ-identityˡ _))))
... | no ¬w'' =
  _ ,
  -ᶜ-⟨⟩-gt ρ≢ᵣuᵣ
    (λ { (ρ'''' , z) → q (ρ' ·ᵣ ρ'''' , trans (cong (ρ' ·ᵣ_) z) (sym (·ᵣ-assoc _ _ _))) })
    (trans s (sym (·ᵣ-assoc _ _ _)))
    (-ᶜ-⟨⟩-gt
      (λ z → ¬w'' (·ᵣ-zero-productˡ z))
      (λ { (ρ'''' , z) →
        ¬w'' (·ᵣ-zero-productʳ (sym (·ᵣ-cancellativeˡ (trans (·ᵣ-identityˡ _) (trans z (sym (·ᵣ-assoc _ _ _))))))) })
      refl t) ,
  id-ren
⟨⟩-μ⁻¹-ren -ʳ ρ , p | no ρ≢ᵣuᵣ = {!!} -- TODO: symmetric to previous case
(⟨⟩-≤-ren p -ʳ ρ , -ᶜ-uᵣ q) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ q)
(⟨⟩-≤-ren p -ʳ ρ , -ᶜ-⟨⟩-lt q s) | no ρ≢ᵣuᵣ = {!!}
(⟨⟩-≤-ren p -ʳ ρ , -ᶜ-⟨⟩-gt q s t u) | no ρ≢ᵣuᵣ = {!!}
(cong-∷-ren r -ʳ ρ , -ᶜ-uᵣ p) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ p)
(cong-∷-ren r -ʳ ρ , -ᶜ-∷ p q) | no ρ≢ᵣuᵣ with r -ʳ ρ , q
... | Γ''' , s , r' =
  Γ''' , -ᶜ-∷ ρ≢ᵣuᵣ s , r'
(cong-⟨⟩-ren r -ʳ ρ , -ᶜ-uᵣ p) | no ρ≢ᵣuᵣ =
  ⊥-elim (ρ≢ᵣuᵣ p)
(cong-⟨⟩-ren r -ʳ ρ , -ᶜ-⟨⟩-lt p q) | no ρ≢ᵣuᵣ =
  _ , -ᶜ-⟨⟩-lt ρ≢ᵣuᵣ q , cong-⟨⟩-ren r
(cong-⟨⟩-ren r -ʳ ρ , -ᶜ-⟨⟩-gt {ρ'' = ρ''} p q s t) | no ρ≢ᵣuᵣ with r -ʳ ρ'' , t
... | Γ''' , u , r' =
  _ , -ᶜ-⟨⟩-gt ρ≢ᵣuᵣ q s u , r'

infixl 30 _-ʳ_,_
