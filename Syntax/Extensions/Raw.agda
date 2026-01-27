----------------------------
-- Raw context extensions --
----------------------------

open import Syntax.Grades

module Syntax.Extensions.Raw (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Data.Product

open import Relation.Binary.PropositionalEquality as Eq hiding ( [_] ) 

open import Syntax.Renamings.Raw (Grades)

open import Syntax.Contexts (Grades)

-- Variable extensions

VExt : Ctx → Ctx → Set
VExt Γ Γ' = ∀ {A ρ} → A ∈[ ρ ] Γ → Σ[ ρ' ∈ R ] A ∈[ ρ' ] Γ'

-- Identity extension

id-vext : ∀ {Γ} → VExt Γ Γ
id-vext {ρ = ρ} x = ρ , x

-- Equality extension

eq-vext : ∀ {Γ Γ'} → Γ ≡ Γ' → VExt Γ Γ'
eq-vext refl = λ x → _ , x

-- Variable extension

var-vext : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → VExt (Γ ∷ A) Γ
var-vext {Γ} {A} {uᵣ} x Hd =
  uᵣ , x
var-vext {Γ} {A} {ρ} x (Tl-∷ {ρ = ρ'} y) =
  ρ' , y

-- Composition of extensions
_∘ᵛᵉ_ : ∀ {Γ Γ' Γ''} → VExt Γ' Γ'' → VExt Γ Γ' → VExt Γ Γ''
_∘ᵛᵉ_ e' e x with e x
... | ρ , y with e' y
... | ρ' , z = ρ' , z

-- Composition of extensions and renamings

_ᵛ∘ʳᵉ_ : ∀ {Γ Γ' Γ''} → VExt Γ' Γ'' → VRen Γ Γ' → VExt Γ Γ''
_ᵛ∘ʳᵉ_ ve vr x with vr x
... | ρ' , rel , y with ve y
... | ρ'' , z = ρ'' , z

_ᵛ∘ᵉʳ_ : ∀ {Γ Γ' Γ''} → VRen Γ' Γ'' → VExt Γ Γ' → VExt Γ Γ''
_ᵛ∘ᵉʳ_ r e x with e x
... | ρ' , y with r y
... | ρ'' , rel' , z = ρ'' , z

-- Weakening extension
{-
wk-∷-vext : ∀ {Γ A} → VExt Γ (Γ ∷ A)
wk-∷-vext {ρ = ρ} x = ρ , Tl-∷ x

wk-⟨⟩-vext : ∀ {Γ ρ} → VExt Γ (Γ ⟨ ρ ⟩)
wk-⟨⟩-vext {ρ = ρ} {ρ = ρ'} x = ρ' ·ᵣ ρ , Tl-⟨⟩ x

wk-ctx-vext : ∀ {Γ Γ'} → VExt Γ (Γ ++ᶜ Γ')
wk-ctx-vext {Γ' = []}      = id-vext
wk-ctx-vext {Γ' = Γ' ∷ A}  = wk-∷-vext ∘ᵛᵉ wk-ctx-vext {Γ' = Γ'}
wk-ctx-vext {Γ} {Γ' ⟨ ρ ⟩} =
  wk-⟨⟩-vext ∘ᵛᵉ wk-ctx-vext {Γ} {Γ'}
-}

-- -- Splitting of an extension context

-- -- split-ext : ∀ {Γ Γ'} → VExt Γ Γ' → Σ[ Γ₁ ∈ Ctx ] (Σ[ Γ₂ ∈ Ctx ] (VRen (Γ₁ ++ᶜ Γ₂) Γ' × VRen Γ₁ Γ))
-- -- split-ext {[]} {Γ'} _  = [] , Γ' , eq-vren ++ᶜ-identityˡ , id-vren
-- -- split-ext {Γ ∷ A}   ve = {!!} , {!!} , (λ x → {!!} , {!!} , {!!}) , λ x → {!!} , {!!} , {!!}
-- -- split-ext {Γ ⟨ ρ ⟩} {Γ'} ve with split-ext {Γ = Γ} {Γ' = Γ'} (ve ᵛ∘ᵉ wk-⟨⟩-vext {ρ = ρ})
-- -- ... | Γ'₁ , Γ'₂ , vr , vrsmaller = {!!} , {!!} , {!!} , {!!}

-- Congruence extensions

cong-∷-vext : ∀ {Γ Γ' A} → VExt Γ Γ' → VExt (Γ ∷ A) (Γ' ∷ A)
cong-∷-vext {Γ' = Γ'} {A = A} vext Hd = uᵣ , Hd
cong-∷-vext {Γ} {Γ'} {A} vext (Tl-∷ x) with vext x
... | ρ , y = ρ , Tl-∷ y

cong-⟨⟩-vext : ∀ {Γ Γ' ρ} → VExt Γ Γ' → VExt (Γ ⟨ ρ ⟩) (Γ' ⟨ ρ ⟩)
cong-⟨⟩-vext {ρ = ρ} vext (Tl-⟨⟩ {ρ' = ρ'} x) with vext x
... | ρ' , y = ρ' ·ᵣ ρ , Tl-⟨⟩ y

-- Congruence of extensions

cong-vext : ∀ {Γ Γ' Γ''} → VExt Γ Γ' → VExt (Γ ++ᶜ Γ'') (Γ' ++ᶜ Γ'')
cong-vext {Γ'' = []} vext        = vext
cong-vext {Γ'' = Γ'' ∷ A} vext   = cong-∷-vext (cong-vext vext)
cong-vext {Γ'' = Γ'' ⟨ ρ ⟩} vext = cong-⟨⟩-vext (cong-vext vext)

{-
empty-ctx-vext : ∀ {Γ} → VExt [] Γ
empty-ctx-vext {[]} = id-vext
empty-ctx-vext {Γ ∷ A} = wk-∷-vext ∘ᵛᵉ empty-ctx-vext {Γ}
empty-ctx-vext {Γ ⟨ ρ ⟩} = wk-⟨⟩-vext ∘ᵛᵉ empty-ctx-vext {Γ}
-}

-- A variable renaming implies a variable extension

vren⇒vext : ∀ {Γ Γ'} → VRen Γ Γ' → VExt Γ Γ'
vren⇒vext vr x = proj₁ (vr x) , proj₂ (proj₂ (vr x))
