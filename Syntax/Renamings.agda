-----------------------
-- Context renamings --
-----------------------

open import Syntax.Grades

module Syntax.Renamings (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Syntax.Contexts (Grades)
--open import Syntax.Language
open import Syntax.Renamings.Raw (Grades) public
open import Syntax.Types (Grades)

open import Util.Equality
open import Util.Time -- remove

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

-- Variable renamings (with an extra condition that disallow discarding time captured by contexts)

record Ren (Γ Γ' : Ctx) : Set where
  constructor ren
  field
    ctx-grade-≾ : ctx-grade Γ ≾ᵣ ctx-grade Γ'
    var-rename : VRen Γ Γ'

open Ren public

-- Lifting the operations on VRen to Ren

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {Γ} =
  ren ≾ᵣ-refl id-vren

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
r' ∘ʳ r =
  ren
    (≾ᵣ-trans (ctx-grade-≾ r) (ctx-grade-≾ r'))
    ((var-rename r') ∘ᵛʳ (var-rename r))

infixr 20 _∘ʳ_

-- Equality renaming

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren p =
  ren
    (≾ᵣ-reflexive (cong ctx-grade p))
    (eq-vren p)

-- Variable weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ A)
wk-ren {Γ} {A} =
  ren ≾ᵣ-refl (wk-vren {Γ} {A})

-- Grade weakening renaming

wk-⟨⟩-ren : ∀ {Γ ρ} → Ren Γ (Γ ⟨ ρ ⟩)
wk-⟨⟩-ren {Γ} {ρ} =
  ren (c≾ᵣc·ᵣd (ctx-grade Γ) ρ) (wk-⟨⟩-vren {Γ} {ρ})

-- Strong monoidal structure of ⟨_⟩

⟨⟩-η-ren : ∀ {Γ} → Ren (Γ ⟨ uᵣ ⟩) Γ
⟨⟩-η-ren {Γ} = 
  ren 
    (ρ-≾ᵣ-substₗ (sym (·ᵣ-identityʳ (ctx-grade Γ))) ≾ᵣ-refl) 
    ⟨⟩-η-vren

⟨⟩-η⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ uᵣ ⟩)
⟨⟩-η⁻¹-ren = wk-⟨⟩-ren

⟨⟩-μ-ren : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ·ᵣ ρ' ⟩) (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩)
⟨⟩-μ-ren {Γ} {ρ} {ρ'} = 
  ren 
    (ρ-≾ᵣ-substₗ (·ᵣ-assoc (ctx-grade Γ) ρ ρ') ≾ᵣ-refl) 
    ⟨⟩-μ-vren

⟨⟩-μ⁻¹-ren : ∀ {Γ ρ ρ'} → Ren (Γ ⟨ ρ ⟩ ⟨ ρ' ⟩) (Γ ⟨ ρ ·ᵣ ρ' ⟩)
⟨⟩-μ⁻¹-ren {Γ} {ρ} {ρ'} = 
  ren 
    (ρ-≾ᵣ-substₗ (sym (·ᵣ-assoc (ctx-grade Γ) ρ ρ')) ≾ᵣ-refl)
    ⟨⟩-μ⁻¹-vren

-- Variable congruence renaming

cong-∷-ren : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
cong-∷-ren ρ =
  ren (ctx-grade-≾ ρ) (cong-∷-vren (var-rename ρ))

-- Grade congruence renaming

cong-⟨⟩-ren : ∀ {Γ Γ' ρ} → Ren Γ Γ' → Ren (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-ren {ρ = ρ} r =
  ren (·ᵣ-monoˡ-≾ᵣ ρ (ctx-grade-≾ r)) (cong-⟨⟩-vren (var-rename r))

-- General congruence renaming

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ} {Γ'} {Γ''} r =
  ren
    (≾ᵣ-trans
      (≾ᵣ-reflexive (ctx-grade-++ᶜ Γ Γ''))
      (≾ᵣ-trans
        (·ᵣ-monoˡ-≾ᵣ (ctx-grade Γ'') (ctx-grade-≾ r))
        (≾ᵣ-reflexive (sym (ctx-grade-++ᶜ Γ' Γ'')))))
    (cong-vren (var-rename r))

-- General weakening renamings

wk-ctx-renᵣ : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-renᵣ {Γ} {Γ'} = 
  ren 
    (ρ-≾ᵣ-substᵣ (ctx-grade-++ᶜ Γ Γ') (c≾ᵣd⇒c≾ᵣd·ᵣb (ctx-grade Γ') ≾ᵣ-refl)) 
    wk-ctx-vren

wk-ctx-renₗ : ∀ {Γ Γ'} → Ren Γ (Γ' ++ᶜ Γ)
wk-ctx-renₗ {Γ} {Γ'} = 
  cong-ren {Γ' = Γ'} (eq-ren ++ᶜ-identityˡ ∘ʳ wk-ctx-renᵣ) 
    ∘ʳ (eq-ren (sym ++ᶜ-identityˡ))

-- Monotonicity renaming for ⟨_⟩

⟨⟩-≤-ren : ∀ {Γ ρ ρ'} → ρ ≾ᵣ ρ' → Ren (Γ ⟨ ρ ⟩) (Γ ⟨ ρ' ⟩)
⟨⟩-≤-ren {Γ} p = 
  ren 
    (·ᵣ-monoʳ-≾ᵣ (ctx-grade Γ) p) 
    (⟨⟩-≾-vren p)

-- Grade and variable exchange renaming

exch-⟨⟩-var-ren : ∀ {Γ A ρ} → Ren (Γ ⟨ ρ ⟩ ∷ A) ((Γ ∷ A) ⟨ ρ ⟩)
exch-⟨⟩-var-ren = 
  ren 
    ≾ᵣ-refl 
    exch-⟨⟩-var-vren

-- Variable exchange renaming

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = 
  ren 
    ≾ᵣ-refl 
    exch-vren


{-
-- Remove
-- Time travelling operation on contexts

_-ʳ_,_ : ∀ {Γ Γ'} → Ren Γ Γ' → (τ : Time) → τ ≤ ctx-grade Γ → Ren (Γ -ᶜ τ) (Γ' -ᶜ τ)
_-ʳ_,_ {Γ} {Γ'} ρ τ p =
  ren
    (≤-trans
      (≤-reflexive (ctx-grade-ᶜ-∸ Γ τ p))
      (≤-trans
        (∸-monoˡ-≤ τ (ctx-grade-≤ ρ))
        (≤-reflexive (sym (ctx-grade-ᶜ-∸ Γ' τ (≤-trans p (ctx-grade-≤ ρ)))))))
    ((var-rename ρ) -ᵛʳ τ)
-}

{-
-- Weakening a time to a context renaming

ren⟨ρ⟩-ctx : ∀ {Γ Γ' ρ} → ρ ≾ᵣ ctx-grade Γ' → Ren (Γ ⟨ ρ ⟩) (Γ ++ᶜ Γ')
ren⟨ρ⟩-ctx {Γ} {Γ'} {ρ} r = ren {!!} {!!} 
-}

{-
ren
    (≤-trans
      (+-monoʳ-≤ (ctx-grade Γ) r)
      (≤-reflexive (sym (ctx-grade-++ᶜ Γ Γ'))))
    (vren⟨τ⟩-ctx p)
-}

-- infixl 30 _-ʳ_,_ -- remove?

-- Reflexivity equality renamings' interaction with identity renamings

eq-ren-refl-id : ∀ {Γ}
               → eq-ren refl ≡ id-ren {Γ}

eq-ren-refl-id {Γ} =
  cong₂ ren (≾ᵣ-irrelevant (≾ᵣ-reflexive refl) ≾ᵣ-refl) refl

-- Congruence renamings' interaction with identities (functoriality)

cong-ren-id : ∀ {Γ Γ'}
            → cong-ren {Γ'' = Γ'} (id-ren {Γ}) ≡ id-ren

cong-ren-id {Γ} {Γ'} =
  cong₂ ren
    (≾ᵣ-irrelevant _ _)
    (ifun-ext (λ {A} → ifun-ext (λ {ρ} → fun-ext (λ x →
      cong-vren-id {Γ} {Γ'} x))))

-- Congruence renamings' interaction with composition (functoriality)

cong-ren-fun : ∀ {Γ Γ' Γ'' Γ'''}
             → (r : Ren Γ Γ')
             → (r' : Ren Γ' Γ'')
             → cong-ren {Γ'' = Γ'''} (r' ∘ʳ r)
             ≡ cong-ren r' ∘ʳ cong-ren r

cong-ren-fun {Γ} {Γ'} {Γ''} {Γ'''} r r' =
  cong₂ ren
    (≾ᵣ-irrelevant _ _)
    (ifun-ext (λ {A} → ifun-ext (λ {ρ} → fun-ext (λ x → cong-vren-fun (var-rename r) (var-rename r') x))))


