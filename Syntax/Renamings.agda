------------------------------------------------------------
-- Context renamings and their action on well-typed terms --
------------------------------------------------------------

module Syntax.Renamings where

open import Data.Product

open import Syntax.Contexts
open import Syntax.Language
open import Syntax.Renamings.Raw public
open import Syntax.Types

open import Util.Equality
open import Util.Time

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

-- Variable renamings (with an extra condition that disallow discarding time captured by contexts)

record Ren (Γ Γ' : Ctx) : Set where
  constructor ren
  field
    ctx-time-≤ : ctx-time Γ ≤ ctx-time Γ'
    var-rename : VRen Γ Γ'

open Ren public

-- Lifting the operations on VRen to Ren

id-ren : ∀ {Γ} → Ren Γ Γ
id-ren {Γ} =
  ren ≤-refl id-vren

-- Composition of renamings

_∘ʳ_ : ∀ {Γ Γ' Γ''} → Ren Γ' Γ'' → Ren Γ Γ' → Ren Γ Γ''
ρ' ∘ʳ ρ =
  ren
    (≤-trans (ctx-time-≤ ρ) (ctx-time-≤ ρ'))
    ((var-rename ρ') ∘ᵛʳ (var-rename ρ))

infixr 20 _∘ʳ_

-- Equality renaming

eq-ren : ∀ {Γ Γ'} → Γ ≡ Γ' → Ren Γ Γ'
eq-ren p =
  ren
    (≤-reflexive (cong ctx-time p))
    (eq-vren p)

-- Variable weakening renaming

wk-ren : ∀ {Γ A} → Ren Γ (Γ ∷ A)
wk-ren {Γ} {A} =
  ren ≤-refl (wk-vren {Γ} {A})

-- Time weakening renaming

wk-⟨⟩-ren : ∀ {Γ τ} → Ren Γ (Γ ⟨ τ ⟩)
wk-⟨⟩-ren {Γ} {τ} =
  ren (m≤m+n (ctx-time Γ) τ) (wk-⟨⟩-vren {Γ} {τ})

-- Strong monoidal structure of ⟨_⟩

⟨⟩-η-ren : ∀ {Γ} → Ren (Γ ⟨ 0 ⟩) Γ
⟨⟩-η-ren {Γ} = 
  ren 
    (τ-≤-substₗ (sym (+-identityʳ (ctx-time Γ))) ≤-refl) 
    ⟨⟩-η-vren

⟨⟩-η⁻¹-ren : ∀ {Γ} → Ren Γ (Γ ⟨ 0 ⟩)
⟨⟩-η⁻¹-ren = wk-⟨⟩-ren

⟨⟩-μ-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ + τ' ⟩) (Γ ⟨ τ ⟩ ⟨ τ' ⟩)
⟨⟩-μ-ren {Γ} {τ} {τ'} = 
  ren 
    (τ-≤-substₗ (+-assoc (ctx-time Γ) τ τ') ≤-refl) 
    ⟨⟩-μ-vren

⟨⟩-μ⁻¹-ren : ∀ {Γ τ τ'} → Ren (Γ ⟨ τ ⟩ ⟨ τ' ⟩) (Γ ⟨ τ + τ' ⟩)
⟨⟩-μ⁻¹-ren {Γ} {τ} {τ'} = 
  ren 
    (τ-≤-substₗ (sym (+-assoc (ctx-time Γ) τ τ')) ≤-refl)
    ⟨⟩-μ⁻¹-vren

-- Variable congruence renaming

cong-∷-ren : ∀ {Γ Γ' A} → Ren Γ Γ' → Ren (Γ ∷ A) (Γ' ∷ A)
cong-∷-ren ρ =
  ren (ctx-time-≤ ρ) (cong-∷-vren (var-rename ρ))

-- Time congruence renaming

cong-⟨⟩-ren : ∀ {Γ Γ' τ} → Ren Γ Γ' → Ren (Γ ⟨ τ ⟩) (Γ' ⟨ τ ⟩)
cong-⟨⟩-ren {τ = τ} ρ =
  ren (+-monoˡ-≤ τ (ctx-time-≤ ρ)) (cong-⟨⟩-vren (var-rename ρ))

-- General congruence renaming

cong-ren : ∀ {Γ Γ' Γ''} → Ren Γ Γ' → Ren (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-ren {Γ} {Γ'} {Γ''} ρ =
  ren
    (≤-trans
      (≤-reflexive (ctx-time-++ᶜ Γ Γ''))
      (≤-trans
        (+-monoˡ-≤ (ctx-time Γ'') (ctx-time-≤ ρ))
        (≤-reflexive (sym (ctx-time-++ᶜ Γ' Γ'')))))
    (cong-vren (var-rename ρ))

-- General weakening renamings

wk-ctx-renᵣ : ∀ {Γ Γ'} → Ren Γ (Γ ++ᶜ Γ')
wk-ctx-renᵣ {Γ} {Γ'} = 
  ren 
    (τ-≤-substᵣ (ctx-time-++ᶜ Γ Γ') (m≤n⇒m≤n+o (ctx-time Γ') ≤-refl)) 
    wk-ctx-vren

wk-ctx-renₗ : ∀ {Γ Γ'} → Ren Γ (Γ' ++ᶜ Γ)
wk-ctx-renₗ {Γ} {Γ'} = 
  cong-ren {Γ' = Γ'} (eq-ren ++ᶜ-identityˡ ∘ʳ wk-ctx-renᵣ) 
    ∘ʳ (eq-ren (sym ++ᶜ-identityˡ))

-- Monotonicity renaming for ⟨_⟩

⟨⟩-≤-ren : ∀ {Γ τ τ'} → τ ≤ τ' → Ren (Γ ⟨ τ ⟩) (Γ ⟨ τ' ⟩)
⟨⟩-≤-ren {Γ} p = 
  ren 
    (+-monoʳ-≤ (ctx-time Γ) p) 
    (⟨⟩-≤-vren p)

-- Time and variable exchange renaming

exch-⟨⟩-var-ren : ∀ {Γ A τ} → Ren (Γ ⟨ τ ⟩ ∷ A) ((Γ ∷ A) ⟨ τ ⟩)
exch-⟨⟩-var-ren = 
  ren 
    ≤-refl 
    exch-⟨⟩-var-vren

-- Variable exchange renaming

exch-ren : ∀ {Γ A B} → Ren (Γ ∷ A ∷ B) (Γ ∷ B ∷ A)
exch-ren = 
  ren 
    ≤-refl 
    exch-vren

-- Time travelling operation on contexts

_-ʳ_,_ : ∀ {Γ Γ'} → Ren Γ Γ' → (τ : Time) → τ ≤ ctx-time Γ → Ren (Γ -ᶜ τ) (Γ' -ᶜ τ)
_-ʳ_,_ {Γ} {Γ'} ρ τ p =
  ren
    (≤-trans
      (≤-reflexive (ctx-time-ᶜ-∸ Γ τ p))
      (≤-trans
        (∸-monoˡ-≤ τ (ctx-time-≤ ρ))
        (≤-reflexive (sym (ctx-time-ᶜ-∸ Γ' τ (≤-trans p (ctx-time-≤ ρ)))))))
    ((var-rename ρ) -ᵛʳ τ)

-- Weakening a time to a context renaming

ren⟨τ⟩-ctx : ∀ {Γ Γ' τ} → τ ≤ ctx-time Γ' → Ren (Γ ⟨ τ ⟩) (Γ ++ᶜ Γ')
ren⟨τ⟩-ctx {Γ} {Γ'} {τ} p =
  ren
    (≤-trans
      (+-monoʳ-≤ (ctx-time Γ) p)
      (≤-reflexive (sym (ctx-time-++ᶜ Γ Γ'))))
    (vren⟨τ⟩-ctx p)

infixl 30 _-ʳ_,_

-- Reflexivity equality renamings' interaction with identity renamings

eq-ren-refl-id : ∀ {Γ}
               → eq-ren refl ≡ id-ren {Γ}
                
eq-ren-refl-id {Γ} =
  cong₂ ren refl refl

-- Congruence renamings' interaction with identities (functoriality)

cong-ren-id : ∀ {Γ Γ'}
            → cong-ren {Γ'' = Γ'} (id-ren {Γ}) ≡ id-ren

cong-ren-id {Γ} {Γ'} =
  cong₂ ren
    (≤-irrelevant _ _)
    (ifun-ext (λ {A} → ifun-ext (λ {τ} → fun-ext (λ x →
      cong-vren-id {Γ} {Γ'} x))))

-- Congruence renamings' interaction with composition (functoriality)

cong-ren-fun : ∀ {Γ Γ' Γ'' Γ'''}
             → (ρ : Ren Γ Γ')
             → (ρ' : Ren Γ' Γ'')
             → cong-ren {Γ'' = Γ'''} (ρ' ∘ʳ ρ)
             ≡ cong-ren ρ' ∘ʳ cong-ren ρ

cong-ren-fun {Γ} {Γ'} {Γ''} {Γ'''} ρ ρ' =
  cong₂ ren
    (≤-irrelevant _ _)
    (ifun-ext (λ {A} → ifun-ext (λ {τ} → fun-ext (λ x → cong-vren-fun (var-rename ρ) (var-rename ρ') x))))

-- Action of renamings on well-typed values and computations

mutual

  V-rename : ∀ {Γ Γ' A}
           → Ren Γ Γ'
           → Γ ⊢V⦂ A
           ------------
           → Γ' ⊢V⦂ A

  V-rename ρ (var x)    = var (proj₂ (proj₂ (var-rename ρ x)))
  V-rename ρ (const c)  = const c
  V-rename ρ ⋆          = ⋆
  V-rename ρ (⦉ V , W ⦊) = ⦉ V-rename ρ V , V-rename ρ W ⦊
  V-rename ρ (lam M)    = lam (C-rename (cong-ren ρ) M)

  C-rename : ∀ {Γ Γ' C}
           → Ren Γ Γ'
           → Γ ⊢C⦂ C
           ------------
           → Γ' ⊢C⦂ C

  C-rename ρ (return V)       = return (V-rename ρ V)
  C-rename ρ (M ; N)          = C-rename ρ M ; C-rename (cong-ren ρ) N
  C-rename ρ (V · W)          = V-rename ρ V · V-rename ρ W
  C-rename ρ (match V `in M)  = match V-rename ρ V `in C-rename (cong-ren ρ) M
  C-rename ρ (absurd V)       = absurd (V-rename ρ V)
  C-rename ρ (perform op V M) = perform op (V-rename ρ V) (C-rename (cong-ren ρ) M)
  C-rename ρ (delay τ M)      = delay τ (C-rename (cong-ren ρ) M)
  C-rename ρ (handle M `with H `in N) =
    handle C-rename ρ M
    `with (λ op τ'' → C-rename (cong-ren ρ) (H op τ'') )
    `in (C-rename (cong-ren ρ) N)
  C-rename ρ (unbox {τ = τ} p V M) =
    unbox (≤-trans p (ctx-time-≤ ρ)) (V-rename (ρ -ʳ τ , p) V) (C-rename (cong-ren ρ) M)
  C-rename ρ (box V M)        = box (V-rename (cong-ren ρ) V) (C-rename (cong-ren ρ) M)
