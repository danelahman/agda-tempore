-----------------------
-- Context renamings --
-----------------------

open import Syntax.Grades

module Syntax.Renamings (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Contexts (Grades)
open import Syntax.Renamings.Raw (Grades) public
open import Syntax.Types (Grades)

open import Util.Equality
open import Util.Time -- remove

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

-- Variable renamings (with an extra condition that disallow discarding time captured by contexts)

record Ren (Γ Γ' : Ctx) : Set where
  constructor ren
  field
    ctx-grade-≾ : ctx-grade Γ' ≾ᵣ ctx-grade Γ
    var-rename : VRen Γ Γ'

open Ren public

-- Lifting the operations on VRen to Ren

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {Γ} = ren ≾ᵣ-refl id-vren

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
r' ∘ʳ r =
  ren
    (≾ᵣ-trans (r' .ctx-grade-≾) (r .ctx-grade-≾))
    ((var-rename r') ∘ᵛʳ (var-rename r))

infixr 20 _∘ʳ_

-- Equality renaming

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren p =
  ren
    (≾ᵣ-reflexive (cong ctx-grade (sym p)))
    (eq-vren p)

-- Variable weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ A)
wk-ren {Γ} {A} =
  ren ≾ᵣ-refl (wk-vren {Γ} {A})

-- Strong monoidal structure of ⟨_⟩

⟨⟩-η-ren : ∀ {Γ} → Ren (Γ ⟨ uᵣ ⟩) Γ
⟨⟩-η-ren {Γ} = 
  ren 
    (c≾ᵣc·ᵣd (ctx-grade Γ) uᵣ)
    ⟨⟩-η-vren

⟨⟩-η⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ uᵣ ⟩)
⟨⟩-η⁻¹-ren {Γ} =
  ren
    (≾ᵣ-reflexive (·ᵣ-identityʳ (ctx-grade Γ)))
    ⟨⟩-η⁻¹-vren

⟨⟩-μ-ren : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
⟨⟩-μ-ren {Γ} {ρ} {ρ'} = 
  ren 
    (≾ᵣ-reflexive (·ᵣ-assoc (ctx-grade Γ) ρ ρ'))
    ⟨⟩-μ-vren

⟨⟩-μ⁻¹-ren : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ' ⟩)
⟨⟩-μ⁻¹-ren {Γ} {ρ} {ρ'} = 
  ren 
    (ρ-≾ᵣ-substᵣ (·ᵣ-assoc (ctx-grade Γ) ρ ρ') ≾ᵣ-refl)
    ⟨⟩-μ⁻¹-vren

-- Variable congruence renaming

cong-∷-ren : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
cong-∷-ren ρ =
  ren
    (ctx-grade-≾ ρ)
    (cong-∷-vren (var-rename ρ))

-- Grade congruence renaming

cong-⟨⟩-ren : ∀ {Γ Γ' ρ} → Ren Γ Γ' → Ren (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-ren {ρ = ρ} r = ren (·ᵣ-monoˡ-≾ᵣ ρ (ctx-grade-≾ r)) (cong-⟨⟩-vren (var-rename r))

-- General congruence renaming

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ} {Γ'} {Γ''} r =
  ren
    (≾ᵣ-trans
      (≾ᵣ-reflexive (ctx-grade-++ᶜ Γ' Γ''))
      (≾ᵣ-trans
        (·ᵣ-monoˡ-≾ᵣ (ctx-grade Γ'') (ctx-grade-≾ r))
        (≾ᵣ-reflexive (sym (ctx-grade-++ᶜ Γ Γ'')))))
    (cong-vren (var-rename r))

-- General weakening renamings

wk-ctx-renᵣ : ∀ {Γ Γ'} → ctx-grade Γ' ≡ uᵣ → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-renᵣ {Γ} {Γ'} rel =
  ren
    (≾ᵣ-reflexive (trans (ctx-grade-++ᶜ Γ Γ') (trans (cong (ctx-grade Γ ·ᵣ_) rel) (·ᵣ-identityʳ (ctx-grade Γ)))))
    (wk-ctx-vren rel)

wk-ctx-renₗ : ∀ {Γ Γ'} → ctx-grade Γ' ≡ uᵣ → Ren Γ (Γ' ++ᶜ Γ)
wk-ctx-renₗ {Γ} {Γ'} rel = 
  cong-ren {Γ' = Γ'} (eq-ren ++ᶜ-identityˡ ∘ʳ wk-ctx-renᵣ rel) 
    ∘ʳ (eq-ren (sym ++ᶜ-identityˡ))

-- Grades substitutions

⟨⟩-≾-ren : ∀ {Γ ρ ρ'} → ρ' ≾ᵣ ρ → Ren (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
⟨⟩-≾-ren {Γ} p = 
  ren 
    (·ᵣ-monoʳ-≾ᵣ (ctx-grade Γ) p) 
    (⟨⟩-≾-vren p)

-- Variable exchange renaming

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = 
  ren 
    ≾ᵣ-refl
    exch-vren

-- Weakening a time to a context renaming

ren⟨ρ⟩-ctx : ∀ {Γ Γ' ρ} → ρ ≡ ctx-grade Γ' → Ren (Γ ⟨ ρ ⟩) (Γ ++ᶜ Γ')
ren⟨ρ⟩-ctx {Γ} {Γ'} {ρ} rel = 
  ren
    (≾ᵣ-trans (≾ᵣ-reflexive (ctx-grade-++ᶜ Γ Γ')) (≾ᵣ-reflexive (cong (ctx-grade Γ ·ᵣ_) (sym rel))))
    (vren⟨ρ⟩-ctx rel)

-- Reflexivity equality renamings' interaction with identity renamings

eq-ren-refl-id : ∀ {Γ} → eq-ren refl ≡ id-ren {Γ}
eq-ren-refl-id {Γ} = cong₂ ren (≾ᵣ-irrelevant _ _) refl

-- Congruence renamings' interaction with identities (functoriality)

cong-ren-id : ∀ {Γ Γ'}
            → cong-ren {Γ'' = Γ'} (id-ren {Γ}) ≡ id-ren

cong-ren-id {Γ} {Γ'} =
  cong₂
    ren
    (≾ᵣ-irrelevant _ _)
    (ifun-ext λ {A} → (ifun-ext λ {ρ} → fun-ext (λ x → cong-vren-id {Γ} {Γ'} x)))

-- Congruence renamings' interaction with composition (functoriality)

cong-ren-fun : ∀ {Γ Γ' Γ'' Γ'''}
             → (r : Ren Γ Γ')
             → (r' : Ren Γ' Γ'')
             → cong-ren {Γ'' = Γ'''} (r' ∘ʳ r)
             ≡ cong-ren r' ∘ʳ cong-ren r

cong-ren-fun {Γ} {Γ'} {Γ''} {Γ'''} r r' =
  cong₂
    ren
    (≾ᵣ-irrelevant _ _)
    (ifun-ext λ {A} → ifun-ext (λ {ρ} → fun-ext (λ x → cong-vren-fun (var-rename r) (var-rename r') x)))

∘ʳ-identityˡ : ∀ {Γ Γ'}
             → (r : Ren Γ Γ')
             → id-ren ∘ʳ r ≡ r
∘ʳ-identityˡ r =
  cong₂
    ren
    (≾ᵣ-irrelevant _ _)
    (ifun-ext λ {A} → ifun-ext λ {ρ} → fun-ext λ x → ∘ᵛʳ-identityˡ (var-rename r) x)

-- One can rename any context into another typing context of neutral grade
ren-ctx-u : (Γ : Ctx) → Σ[ Γ' ∈ Ctx ] (ctx-grade Γ' ≡ uᵣ × Ren Γ Γ')
ren-ctx-u [] = [] , refl , id-ren
ren-ctx-u (Γ ∷ A) with ren-ctx-u Γ
... | Γ' , rel , r = Γ' ∷ A , rel , cong-ren r
ren-ctx-u (Γ ⟨ ρ ⟩) with ren-ctx-u Γ
... | Γ' , rel , r =
  Γ' , rel , ren (c≾ᵣd⇒c≾ᵣd·ᵣb ρ (ctx-grade-≾ r)) ((var-rename r ∘ᵛʳ ⟨⟩-η-vren) ∘ᵛʳ ⟨⟩-≾-vren uᵣ≾ᵣc)
