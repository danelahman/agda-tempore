--------------------------------------------
-- Variables and contexts of the language --
--------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Binary.Definitions
open import Relation.Nullary

open import Grades.Base
open import Language.Spec

open import Util.Equality

module ClosedCalculus.Syntax.Contexts (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import ClosedCalculus.Syntax.Types S

-- Structured contexts

data Ctx : Set where
  []   : Ctx                    -- empty context
  _∷_  : Ctx → VType → Ctx      -- context extension with a variable
  _⟨_⟩ : Ctx → R → Ctx          -- using context after time-passage

infixl 31 _∷_
infix  32 _⟨_⟩

∷ᶜ-injective-ctx : ∀ {Γ Γ' A B} → Γ ∷ A ≡ Γ' ∷ B → Γ ≡ Γ'
∷ᶜ-injective-ctx refl = refl

∷ᶜ-injective-ty : ∀ {Γ Γ' A B} → Γ ∷ A ≡ Γ' ∷ B → A ≡ B
∷ᶜ-injective-ty refl = refl

⟨⟩-injective-ctx : ∀ {Γ Γ' ρ ρ'} → Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ' ⟩ → Γ ≡ Γ'
⟨⟩-injective-ctx refl = refl

⟨⟩-injective-rgrade : ∀ {Γ Γ' ρ ρ'} → Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ' ⟩ → ρ ≡ ρ'
⟨⟩-injective-rgrade refl = refl

-- Concatenation of contexts

_++ᶜ_ : Ctx → Ctx → Ctx
Γ ++ᶜ []         = Γ
Γ ++ᶜ (Γ' ∷ A)   = (Γ ++ᶜ Γ') ∷ A
Γ ++ᶜ (Γ' ⟨ ρ ⟩) = (Γ ++ᶜ Γ') ⟨ ρ ⟩

infixl 30 _++ᶜ_

-- Identity, associativity, congruence, and injectivity of ++ᶜ

++ᶜ-identityˡ : ∀ {Γ} → [] ++ᶜ Γ ≡ Γ
++ᶜ-identityˡ {[]}      = refl
++ᶜ-identityˡ {Γ ∷ A}   = cong (_∷ A) ++ᶜ-identityˡ
++ᶜ-identityˡ {Γ ⟨ ρ ⟩} = cong (_⟨ ρ ⟩) ++ᶜ-identityˡ

-- Same concatenation, recursing on the left argument: `[] ⋈ᶜ Δ` reduces to
-- `Δ` definitionally, where `[] ++ᶜ Δ` only holds propositionally.

_⋈ᶜ_ : Ctx → Ctx → Ctx
[] ⋈ᶜ Δ        = Δ
(Ξ ∷ A) ⋈ᶜ Δ   = (Ξ ∷ A) ++ᶜ Δ
(Ξ ⟨ ρ ⟩) ⋈ᶜ Δ = (Ξ ⟨ ρ ⟩) ++ᶜ Δ

infixl 30 _⋈ᶜ_

⋈ᶜ-++ᶜ : (Ξ Δ : Ctx) → Ξ ⋈ᶜ Δ ≡ Ξ ++ᶜ Δ
⋈ᶜ-++ᶜ []        Δ = sym ++ᶜ-identityˡ
⋈ᶜ-++ᶜ (Ξ ∷ A)   Δ = refl
⋈ᶜ-++ᶜ (Ξ ⟨ ρ ⟩) Δ = refl

++ᶜ-assoc : (Γ Γ' Γ'' : Ctx) → (Γ ++ᶜ Γ') ++ᶜ Γ'' ≡ Γ ++ᶜ (Γ' ++ᶜ Γ'')
++ᶜ-assoc Γ Γ' []          = refl
++ᶜ-assoc Γ Γ' (Γ'' ∷ A)   = cong (_∷ A) (++ᶜ-assoc Γ Γ' Γ'')
++ᶜ-assoc Γ Γ' (Γ'' ⟨ ρ ⟩) = cong (_⟨ ρ ⟩) (++ᶜ-assoc Γ Γ' Γ'')

++ᶜ-identityʳ-unique : ∀ {Γ Γ'} → Γ ≡ Γ ++ᶜ Γ' → Γ' ≡ []
++ᶜ-identityʳ-unique {Γ} {[]} p =
  refl
++ᶜ-identityʳ-unique {Γ ∷ A} {Γ' ∷ B} p
  with ++ᶜ-identityʳ-unique {Γ} {[] ∷ A ++ᶜ Γ'}
         (trans (∷ᶜ-injective-ctx p) (++ᶜ-assoc Γ ([] ∷ A) Γ'))
++ᶜ-identityʳ-unique {Γ ∷ A} {[] ∷ B} p | ()
++ᶜ-identityʳ-unique {Γ ∷ A} {Γ' ∷ _ ∷ B} p | ()
++ᶜ-identityʳ-unique {Γ ∷ A} {Γ' ⟨ _ ⟩ ∷ B} p | ()
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {Γ' ⟨ ρ' ⟩} p
  with ++ᶜ-identityʳ-unique {Γ} {[] ⟨ ρ ⟩ ++ᶜ Γ'}
         (trans (⟨⟩-injective-ctx p) (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Γ'))
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {[] ⟨ ρ' ⟩} p | ()
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {(Γ' ∷ _) ⟨ ρ' ⟩} p | ()
++ᶜ-identityʳ-unique {Γ ⟨ ρ ⟩} {(Γ' ⟨ _ ⟩) ⟨ ρ' ⟩} p | ()

++ᶜ-inj₂ : ∀ {Γ Γ₁ Γ₂} → Γ ++ᶜ Γ₁ ≡ Γ ++ᶜ Γ₂ → Γ₁ ≡ Γ₂
++ᶜ-inj₂ {Γ} {[]} {[]} q =
  refl
++ᶜ-inj₂ {Γ} {[]} {Γ₂ ∷ B} q =
  sym (++ᶜ-identityʳ-unique q)
++ᶜ-inj₂ {Γ} {[]} {Γ₂ ⟨ ρ' ⟩} q =
  sym (++ᶜ-identityʳ-unique q)
++ᶜ-inj₂ {Γ} {Γ₁ ∷ A} {[]} q =
  ++ᶜ-identityʳ-unique (sym q)
++ᶜ-inj₂ {Γ} {Γ₁ ∷ A} {Γ₂ ∷ B} q =
  cong₂ _∷_ (++ᶜ-inj₂ (∷ᶜ-injective-ctx q)) (∷ᶜ-injective-ty q)
++ᶜ-inj₂ {Γ} {Γ₁ ⟨ ρ ⟩} {[]} q =
  ++ᶜ-identityʳ-unique (sym q)
++ᶜ-inj₂ {Γ} {Γ₁ ⟨ ρ ⟩} {Γ₂ ⟨ ρ' ⟩} q =
  cong₂ _⟨_⟩ (++ᶜ-inj₂ (⟨⟩-injective-ctx q)) (⟨⟩-injective-rgrade q)

-- Amount of time-passage modelled by a context 

ctx-grade : Ctx → R
ctx-grade []        = uᵣ
ctx-grade (Γ ∷ A)   = ctx-grade Γ
ctx-grade (Γ ⟨ ρ ⟩) = ctx-grade Γ ·ᵣ ρ

-- Interaction of time-passage and ++ᶜ

ctx-grade-++ᶜ : (Γ Γ' : Ctx)
              → ctx-grade (Γ ++ᶜ Γ') ≃ᵣ (ctx-grade Γ ·ᵣ ctx-grade Γ')
ctx-grade-++ᶜ Γ []         = ≃ᵣ-sym (·ᵣ-identityʳ (ctx-grade Γ))
ctx-grade-++ᶜ Γ (Γ' ∷ x)   = ctx-grade-++ᶜ Γ Γ'
ctx-grade-++ᶜ Γ (Γ' ⟨ ρ ⟩) = ≃ᵣ-trans (·ᵣ-cong (ctx-grade-++ᶜ Γ Γ') ≃ᵣ-refl)
                             (·ᵣ-assoc (ctx-grade Γ) (ctx-grade Γ') ρ)

-- Proof that sub-contexts split a given context

data _,_split_ : (Γ Γ' Γ'' : Ctx) → Set where
  split-[] : ∀ {Γ} → Γ , [] split Γ
  split-∷  : ∀ {Γ Γ' Γ'' A} → Γ , Γ' split Γ'' → Γ , Γ' ∷ A split Γ'' ∷ A
  split-⟨⟩ : ∀ {Γ Γ' Γ'' ρ} → Γ , Γ' split Γ'' → Γ , Γ' ⟨ ρ ⟩ split Γ'' ⟨ ρ ⟩

-- Interaction between context splitting and ++ᶜ 

split-≡ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → Γ₁ ++ᶜ Γ₂ ≡ Γ
split-≡ split-[]     = refl
split-≡ (split-∷ c)  = cong (_∷ _) (split-≡ c)
split-≡ (split-⟨⟩ c) = cong (_⟨ _ ⟩) (split-≡ c)

≡-split : ∀ {Γ Γ₁ Γ₂} → Γ₁ ++ᶜ Γ₂ ≡ Γ → Γ₁ , Γ₂ split Γ
≡-split {Γ₂ = []}       refl = split-[]
≡-split {Γ₂ = Γ₂ ∷ A}   refl = split-∷ (≡-split refl)
≡-split {Γ₂ = Γ₂ ⟨ ρ ⟩} refl = split-⟨⟩ (≡-split refl)

split-≡-++ᶜ : ∀ {Γ₁ Γ₂} → Γ₁ , Γ₂ split (Γ₁ ++ᶜ Γ₂)
split-≡-++ᶜ = ≡-split refl

-- Variable in a context (under ρ-amount of time-passage)

data _∈[_]_ (A : VType) : R → Ctx → Set where
  Hd    : ∀ {Γ}      → A ∈[ uᵣ ] Γ ∷ A
  Tl-∷  : ∀ {Γ B ρ}  → A ∈[ ρ ] Γ → A ∈[ ρ ] Γ ∷ B
  Tl-⟨⟩ : ∀ {Γ ρ ρ'} → A ∈[ ρ' ] Γ → A ∈[ ρ' ·ᵣ ρ ] Γ ⟨ ρ ⟩

infix 27 _∈[_]_

∈-ctx-extensionˡ : ∀ {A ρ} → (Γ : Ctx) → (Γ' : Ctx) → A ∈[ ρ ] Γ' → A ∈[ ρ ] Γ ++ᶜ Γ'
∈-ctx-extensionˡ _ _ Hd = Hd
∈-ctx-extensionˡ Γ _ (Tl-∷ x) = Tl-∷ (∈-ctx-extensionˡ Γ _ x)
∈-ctx-extensionˡ Γ _ (Tl-⟨⟩ x) = Tl-⟨⟩ (∈-ctx-extensionˡ Γ _ x)


-- Splitting a context according to a variable in it

var-split : ∀ {Γ A ρ}
          → A ∈[ ρ ] Γ
          → Σ[ Γ₁ ∈ Ctx ] Σ[ Γ₂ ∈ Ctx ] Γ₁ ∷ A , Γ₂ split Γ × ctx-grade Γ₂ ≡ ρ
var-split (Hd {Γ}) = Γ , [] , split-[] , refl
var-split {Γ ∷ B} (Tl-∷ x) with var-split x
... | Γ₁ , Γ₂ , p₁ , e = Γ₁ , Γ₂ ∷ B , split-∷ p₁ , e
var-split {Γ ⟨ ρ ⟩} (Tl-⟨⟩ x) with var-split x
... | Γ₁ , Γ₂ , p , q =
  Γ₁ , Γ₂ ⟨ ρ ⟩ , split-⟨⟩ p , cong (_·ᵣ ρ) q

-- Named accessors for the components of `var-split`.

split-l : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → Ctx
split-l x = proj₁ (var-split x)

split-r : ∀ {Γ A ρ} → A ∈[ ρ ] Γ → Ctx
split-r x = proj₁ (proj₂ (var-split x))

split-pf : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → split-l x ∷ A , split-r x split Γ
split-pf x = proj₁ (proj₂ (proj₂ (var-split x)))

split-grade-≡ : ∀ {Γ A ρ} → (x : A ∈[ ρ ] Γ) → ctx-grade (split-r x) ≡ ρ
split-grade-≡ x = proj₂ (proj₂ (proj₂ (var-split x)))
  

-- Grade-only contexts

data ⟨⟩-Ctx : Ctx → Set where
  is-[] : ⟨⟩-Ctx []
  is-⟨⟩ : ∀ {Γ ρ} → ⟨⟩-Ctx Γ → ⟨⟩-Ctx (Γ ⟨ ρ ⟩)


-- A variable of the local part is one of the join; at the empty ambient this
-- is the identity, definitionally.

∈-⋈ᶜ : ∀ {Δ A ρ} → (Ξ : Ctx) → A ∈[ ρ ] Δ → A ∈[ ρ ] (Ξ ⋈ᶜ Δ)
∈-⋈ᶜ []        x = x
∈-⋈ᶜ (Ξ ∷ A)   x = ∈-ctx-extensionˡ (Ξ ∷ A) _ x
∈-⋈ᶜ (Ξ ⟨ ρ ⟩) x = ∈-ctx-extensionˡ (Ξ ⟨ ρ ⟩) _ x

-- Reassociating a prefix of the ambient into the local part.

⋈ᶜ-assoc : (Ξ Δ Δ₀ : Ctx) → (Ξ ⋈ᶜ Δ) ⋈ᶜ Δ₀ ≡ Ξ ⋈ᶜ (Δ ++ᶜ Δ₀)
⋈ᶜ-assoc []        Δ Δ₀ = ⋈ᶜ-++ᶜ Δ Δ₀
⋈ᶜ-assoc (Ξ ∷ A)   Δ Δ₀ =
  trans (⋈ᶜ-++ᶜ ((Ξ ∷ A) ++ᶜ Δ) Δ₀) (++ᶜ-assoc (Ξ ∷ A) Δ Δ₀)
⋈ᶜ-assoc (Ξ ⟨ ρ ⟩) Δ Δ₀ =
  trans (⋈ᶜ-++ᶜ ((Ξ ⟨ ρ ⟩) ++ᶜ Δ) Δ₀) (++ᶜ-assoc (Ξ ⟨ ρ ⟩) Δ Δ₀)

-- Appending a context on the right of a split.

split-++ʳ : ∀ {Γ Γ₁ Γ₂} → Γ₁ , Γ₂ split Γ → (D : Ctx) → Γ₁ , Γ₂ ++ᶜ D split (Γ ++ᶜ D)
split-++ʳ s []        = s
split-++ʳ s (D ∷ B)   = split-∷ (split-++ʳ s D)
split-++ʳ s (D ⟨ ρ ⟩) = split-⟨⟩ (split-++ʳ s D)

-- The variable a split points at, so it can be substituted into by `_[_↦_]c`.

split→∈ : ∀ {Γ Γ₁ Γ₂ A} → Γ₁ ∷ A , Γ₂ split Γ → A ∈[ ctx-grade Γ₂ ] Γ
split→∈ split-[]     = Hd
split→∈ (split-∷ s)  = Tl-∷ (split→∈ s)
split→∈ (split-⟨⟩ s) = Tl-⟨⟩ (split→∈ s)
