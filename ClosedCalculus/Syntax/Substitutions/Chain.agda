------------------------------------------------------
-- Parallel substitutions: composition taken freely   --
------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary

open import Grades.Base
open import Language.Spec

open import Util.Equality

module ClosedCalculus.Syntax.Substitutions.Chain (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import ClosedCalculus.Syntax.Contexts   S
open import ClosedCalculus.Syntax.Terms      S
open import ClosedCalculus.Syntax.RenActions S
open import ClosedCalculus.Syntax.Renamings  S
open import Language.Types                   S

open import ClosedCalculus.Syntax.Substitutions.Base      S
open import ClosedCalculus.Syntax.Substitutions.Lookup S
open import ClosedCalculus.Syntax.Substitutions.Action    S

-- A `Sub Ξ Δ Δ'` is a chain of generating substitutions, read from its source:
-- the composite of `s : Sub₀ Ξ Δ Δ₀` with a chain out of `Δ₀`. Composition is
-- therefore concatenation, and is associative and unital as an equation rather
-- than up to an observation.
--
-- Taking composition freely keeps the two recursions of `Sub₀` apart: neither
-- `sub-var₀` nor the action on terms ever sees a chain.

infixr 5 _◅_

data Sub (Ξ : Ctx) : Ctx → Ctx → Set where
  []ˢ : ∀ {Δ} → Sub Ξ Δ Δ
  _◅_ : ∀ {Δ Δ' Δ''} → Sub₀ Ξ Δ Δ' → Sub Ξ Δ' Δ'' → Sub Ξ Δ Δ''

-- A single generator, and a renaming, as chains.

[_]ˢ : ∀ {Ξ Δ Δ'} → Sub₀ Ξ Δ Δ' → Sub Ξ Δ Δ'
[ s ]ˢ = s ◅ []ˢ

⌜_⌝ˢ : ∀ {Ξ Δ Δ'} → Ren Ξ Δ Δ' → Sub Ξ Δ Δ'
⌜ r ⌝ˢ = [ ⌜ r ⌝ ]ˢ

-- Composition is concatenation, recursing on the second argument, so the
-- right unit law holds definitionally.

infixr 20 _∘ˢ_

_∘ˢ_ : ∀ {Ξ Δ Δ' Δ''} → Sub Ξ Δ' Δ'' → Sub Ξ Δ Δ' → Sub Ξ Δ Δ''
σ₂ ∘ˢ []ˢ      = σ₂
σ₂ ∘ˢ (s ◅ σ₁) = s ◅ (σ₂ ∘ˢ σ₁)

-- Every `Sub₀ → Sub₀` map applies a functor to both endpoints and possibly
-- moves the ambient, so all of them are this one map.

mapˢ : ∀ {Ξ Ξ' Δ Δ'} → (F : Ctx → Ctx)
     → (∀ {Δ₀ Δ₀'} → Sub₀ Ξ Δ₀ Δ₀' → Sub₀ Ξ' (F Δ₀) (F Δ₀'))
     → Sub Ξ Δ Δ'
     → Sub Ξ' (F Δ) (F Δ')
mapˢ F g []ˢ      = []ˢ
mapˢ F g (s ◅ σ) = g s ◅ mapˢ F g σ

cong-∷-subˢ : ∀ {Ξ Δ Δ' A} → Sub Ξ Δ Δ' → Sub Ξ (Δ ∷ A) (Δ' ∷ A)
cong-∷-subˢ {A = A} = mapˢ (_∷ A) cong-∷-sub

cong-⟨⟩-subˢ : ∀ {Ξ Δ Δ' ρ} → Sub Ξ Δ Δ' → Sub Ξ (Δ ⟨ ρ ⟩) (Δ' ⟨ ρ ⟩)
cong-⟨⟩-subˢ {ρ = ρ} = mapˢ (_⟨ ρ ⟩) cong-⟨⟩-sub

-- Recursion on the suffix, as `cong-sub₀` is, so that a concrete suffix peels
-- one congruence at a time and the empty one is the substitution itself.

cong-subˢ : ∀ {Ξ Δ Δ' Γ''} → Sub Ξ Δ Δ' → Sub Ξ (Δ ++ᶜ Γ'') (Δ' ++ᶜ Γ'')
cong-subˢ {Γ'' = []}        σ = σ
cong-subˢ {Γ'' = Γ'' ∷ A}   σ = cong-∷-subˢ (cong-subˢ σ)
cong-subˢ {Γ'' = Γ'' ⟨ ρ ⟩} σ = cong-⟨⟩-subˢ (cong-subˢ σ)

expose-subˢ : ∀ {Ξ Δ₀ Δ₀'} → (Δ : Ctx) → Sub (Ξ ⋈ᶜ Δ) Δ₀ Δ₀'
            → Sub Ξ (Δ ++ᶜ Δ₀) (Δ ++ᶜ Δ₀')
expose-subˢ Δ = mapˢ (Δ ++ᶜ_) (expose-sub₀ Δ)

expose-subˢ-[] : ∀ {Ξ Δ Δ'} → Sub Ξ Δ Δ' → Sub [] (Ξ ++ᶜ Δ) (Ξ ++ᶜ Δ')
expose-subˢ-[] {Ξ} s = expose-subˢ Ξ s

-- Recursion on the chain alone: each step is the already-defined action of a
-- generator. A one-step chain acts as its generator does, definitionally.

V-sub : ∀ {Γ Γ' A} → Sub [] Γ Γ' → Γ' ⊢V⦂ A → Γ ⊢V⦂ A
V-sub []ˢ      V = V
V-sub (s ◅ σ) V = V-sub₀ s (V-sub σ V)

C-sub : ∀ {Γ Γ' C} → Sub [] Γ Γ' → Γ' ⊢C⦂ C → Γ ⊢C⦂ C
C-sub []ˢ      M = M
C-sub (s ◅ σ) M = C-sub₀ s (C-sub σ M)

-- A variable's image is read off by acting on it, which unfolds to the fold of
-- `sub-var₀` along the chain: each later step substitutes into the value the
-- earlier ones produced.

sub-var : ∀ {Δ Δ' A ρ}
        → Sub [] Δ Δ'
        → A ∈[ ρ ] Δ'
        → (¬ Eternal A → ρ ≾ᵣ uᵣ)
        ---------------------------
        → Δ ⊢V⦂ A

sub-var σ x f = V-sub σ (var f x)

-- A resource variable's image stays a variable, its grade dropping once per
-- step.

sub-tgt : ∀ {Δ Δ' A ρ ρ'}
        → Sub [] Δ Δ'
        → [ ρ ] A ∈[ ρ' ] Δ'
        ----------------------------------------------------
        → Σ[ ρ₀ ∈ R ] Σ[ A₀ ∈ VType ] Σ[ ρ'' ∈ R ]
            (([ ρ₀ ] A₀ ∈[ ρ'' ] Δ)
              × (([ ρ₀ ] A₀) <:ᵛ ([ ρ ] A)) × (ρ'' ≾ᵣ ρ'))

sub-tgt {A = A} {ρ = ρ} []ˢ y =
  ρ , A , _ , y , <:ᵛ-refl ([ ρ ] A) , ≾ᵣ-refl
sub-tgt (s ◅ σ) y =
  let (ρ₀ , A₀ , ρ'' , z , w , g) = sub-tgt σ y in
  tgt-grade₀ s z , tgt-type₀ s z , tgt-elapsed₀ s z
  , tgt-var₀ s z , <:ᵛ-trans (tgt-<:₀ s z) w , ≾ᵣ-trans (tgt-≾₀ s z) g

-- All by induction on the chain: no recursion over terms anywhere.

∘ˢ-identityʳ : ∀ {Ξ Δ Δ'} → (σ : Sub Ξ Δ Δ') → σ ∘ˢ []ˢ ≡ σ
∘ˢ-identityʳ σ = refl

∘ˢ-identityˡ : ∀ {Ξ Δ Δ'} → (σ : Sub Ξ Δ Δ') → []ˢ ∘ˢ σ ≡ σ
∘ˢ-identityˡ []ˢ      = refl
∘ˢ-identityˡ (s ◅ σ) = cong (s ◅_) (∘ˢ-identityˡ σ)

∘ˢ-assoc : ∀ {Ξ Δ Δ' Δ'' Δ'''}
         → (σ₃ : Sub Ξ Δ'' Δ''') → (σ₂ : Sub Ξ Δ' Δ'') → (σ₁ : Sub Ξ Δ Δ')
         → ((σ₃ ∘ˢ σ₂) ∘ˢ σ₁) ≡ (σ₃ ∘ˢ (σ₂ ∘ˢ σ₁))
∘ˢ-assoc σ₃ σ₂ []ˢ      = refl
∘ˢ-assoc σ₃ σ₂ (s ◅ σ₁) = cong (s ◅_) (∘ˢ-assoc σ₃ σ₂ σ₁)

-- The action of a composite is the composite of the actions. The chain is the
-- only thing recursed on, the two actions being applied to the same term.

V-sub-∘ˢ : ∀ {Γ Γ' Γ'' A}
         → (σ₂ : Sub [] Γ' Γ'') → (σ₁ : Sub [] Γ Γ') → (V : Γ'' ⊢V⦂ A)
         → V-sub (σ₂ ∘ˢ σ₁) V ≡ V-sub σ₁ (V-sub σ₂ V)
V-sub-∘ˢ σ₂ []ˢ      V = refl
V-sub-∘ˢ σ₂ (s ◅ σ₁) V = cong (V-sub₀ s) (V-sub-∘ˢ σ₂ σ₁ V)

C-sub-∘ˢ : ∀ {Γ Γ' Γ'' C}
         → (σ₂ : Sub [] Γ' Γ'') → (σ₁ : Sub [] Γ Γ') → (M : Γ'' ⊢C⦂ C)
         → C-sub (σ₂ ∘ˢ σ₁) M ≡ C-sub σ₁ (C-sub σ₂ M)
C-sub-∘ˢ σ₂ []ˢ      M = refl
C-sub-∘ˢ σ₂ (s ◅ σ₁) M = cong (C-sub₀ s) (C-sub-∘ˢ σ₂ σ₁ M)

-- Every chain-level map is a functor for composition, since it is `mapˢ`.

mapˢ-∘ˢ : ∀ {Ξ Ξ' Δ Δ' Δ''} → (F : Ctx → Ctx)
        → (g : ∀ {Δ₀ Δ₀'} → Sub₀ Ξ Δ₀ Δ₀' → Sub₀ Ξ' (F Δ₀) (F Δ₀'))
        → (σ₂ : Sub Ξ Δ' Δ'') → (σ₁ : Sub Ξ Δ Δ')
        → mapˢ F g (σ₂ ∘ˢ σ₁) ≡ (mapˢ F g σ₂ ∘ˢ mapˢ F g σ₁)
mapˢ-∘ˢ F g σ₂ []ˢ      = refl
mapˢ-∘ˢ F g σ₂ (s ◅ σ₁) = cong (g s ◅_) (mapˢ-∘ˢ F g σ₂ σ₁)
