------------------------------------------------------------------
-- Skeletons: open types with every grade slot deleted            --
--                                                                --
-- A skeleton records the shape of an open type and nothing else: --
-- the box grade, the arrow's effect grade and the effect grade   --
-- of a computation type are dropped, so a computation type       --
-- contributes the skeleton of its value part alone.              --
--                                                                --
-- Skeleton variables are a sort of their own, drawn from a bare  --
-- `Fin`; `skelᵛ` sends each type variable to the skeleton        --
-- variable of the same index, so unifying two skeleton variables --
-- records that two type variables have the same shape without    --
-- identifying them.                                              --
--                                                                --
-- Substitution, `_forᵏ_` and `checkᵏ` follow McBride's           --
-- structural unification (JFP 2003), here at one sort.           --
------------------------------------------------------------------

open import Data.Fin.Base using (Fin; punchIn)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′) renaming (map to mmap)
open import Data.Nat.Base using (ℕ; suc)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.SolverImpl.Core.Skel (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S using (BaseType)

open import TypeInference.Open.Grades S
open import TypeInference.Open.Types  S

open import TypeInference.SolverImpl.Core.Thick
open import TypeInference.SolverImpl.Core.Rigid S using (zip₂)

infix  37 sBox_
infix  32 _s×_
infixr 30 _s⇒_

data Skel (n : ℕ) : Set where
  svar   : Fin n → Skel n                  -- skeleton variable
  sBase  : BaseType → Skel n               -- base types
  sUnit  : Skel n                          -- unit type
  sBool  : Skel n                          -- boolean type
  _s×_   : Skel n → Skel n → Skel n        -- product type
  sEmpty : Skel n                          -- empty type
  _s⇒_   : Skel n → Skel n → Skel n        -- function type, to its result's value part
  sBox_  : Skel n → Skel n                 -- box modality

-- A skeleton that is still a variable

svar? : ∀ {n} → Skel n → Maybe (Fin n)
svar? (svar γ) = just γ
svar? _        = nothing

svar?-just : ∀ {n} → (t : Skel n) → {γ : Fin n} → svar? t ≡ just γ → t ≡ svar γ
svar?-just (svar γ)  refl = refl
svar?-just (sBase b) ()
svar?-just sUnit     ()
svar?-just sBool     ()
svar?-just (t s× u)  ()
svar?-just sEmpty    ()
svar?-just (t s⇒ u)  ()
svar?-just (sBox t)  ()

-- The skeleton of an open type

mutual

  skelᵛ : ∀ {Ψ} → OVType Ψ → Skel (nTy Ψ)
  skelᵛ (tvar α)  = svar α
  skelᵛ (Base b)  = sBase b
  skelᵛ Unit      = sUnit
  skelᵛ Bool      = sBool
  skelᵛ (A |×| B) = skelᵛ A s× skelᵛ B
  skelᵛ Empty     = sEmpty
  skelᵛ (A ⇒ C)   = skelᵛ A s⇒ skelᶜ C
  skelᵛ ([ ρ ] A) = sBox skelᵛ A

  skelᶜ : ∀ {Ψ} → OCType Ψ → Skel (nTy Ψ)
  skelᶜ (A ‼ ε) = skelᵛ A

-- Substitutions of skeleton variables

SSub : ℕ → ℕ → Set
SSub n m = Fin n → Skel m

infixl 50 _[_]ᵏ
infixl 25 _⨟ᵏ_
infix  20 _≐ᵏ_

_[_]ᵏ : ∀ {n m} → Skel n → SSub n m → Skel m
svar α    [ σ ]ᵏ = σ α
sBase b   [ σ ]ᵏ = sBase b
sUnit     [ σ ]ᵏ = sUnit
sBool     [ σ ]ᵏ = sBool
(t s× u)  [ σ ]ᵏ = t [ σ ]ᵏ s× u [ σ ]ᵏ
sEmpty    [ σ ]ᵏ = sEmpty
(t s⇒ u)  [ σ ]ᵏ = t [ σ ]ᵏ s⇒ u [ σ ]ᵏ
(sBox t)  [ σ ]ᵏ = sBox t [ σ ]ᵏ

idᵏ : ∀ {n} → SSub n n
idᵏ = svar

_⨟ᵏ_ : ∀ {n m l} → SSub n m → SSub m l → SSub n l
(σ ⨟ᵏ δ) α = σ α [ δ ]ᵏ

-- Pointwise equality of substitutions (avoids function extensionality)

_≐ᵏ_ : ∀ {n m} → SSub n m → SSub n m → Set
σ ≐ᵏ δ = ∀ α → σ α ≡ δ α

[id]ᵏ : ∀ {n} → (t : Skel n) → t [ idᵏ ]ᵏ ≡ t
[id]ᵏ (svar α)  = refl
[id]ᵏ (sBase b) = refl
[id]ᵏ sUnit     = refl
[id]ᵏ sBool     = refl
[id]ᵏ (t s× u)  = cong₂ _s×_ ([id]ᵏ t) ([id]ᵏ u)
[id]ᵏ sEmpty    = refl
[id]ᵏ (t s⇒ u)  = cong₂ _s⇒_ ([id]ᵏ t) ([id]ᵏ u)
[id]ᵏ (sBox t)  = cong sBox_ ([id]ᵏ t)

[⨟]ᵏ : ∀ {n m l} → (t : Skel n) → (σ : SSub n m) → (δ : SSub m l)
     → t [ σ ]ᵏ [ δ ]ᵏ ≡ t [ σ ⨟ᵏ δ ]ᵏ
[⨟]ᵏ (svar α)  σ δ = refl
[⨟]ᵏ (sBase b) σ δ = refl
[⨟]ᵏ sUnit     σ δ = refl
[⨟]ᵏ sBool     σ δ = refl
[⨟]ᵏ (t s× u)  σ δ = cong₂ _s×_ ([⨟]ᵏ t σ δ) ([⨟]ᵏ u σ δ)
[⨟]ᵏ sEmpty    σ δ = refl
[⨟]ᵏ (t s⇒ u)  σ δ = cong₂ _s⇒_ ([⨟]ᵏ t σ δ) ([⨟]ᵏ u σ δ)
[⨟]ᵏ (sBox t)  σ δ = cong sBox_ ([⨟]ᵏ t σ δ)

[≐]ᵏ : ∀ {n m} {σ δ : SSub n m} → σ ≐ᵏ δ → (t : Skel n) → t [ σ ]ᵏ ≡ t [ δ ]ᵏ
[≐]ᵏ p (svar α)  = p α
[≐]ᵏ p (sBase b) = refl
[≐]ᵏ p sUnit     = refl
[≐]ᵏ p sBool     = refl
[≐]ᵏ p (t s× u)  = cong₂ _s×_ ([≐]ᵏ p t) ([≐]ᵏ p u)
[≐]ᵏ p sEmpty    = refl
[≐]ᵏ p (t s⇒ u)  = cong₂ _s⇒_ ([≐]ᵏ p t) ([≐]ᵏ p u)
[≐]ᵏ p (sBox t)  = cong sBox_ ([≐]ᵏ p t)

-- The substitution that eliminates one skeleton variable

infix 40 _forᵏ_

_forᵏ_ : ∀ {n} → Skel n → Fin (suc n) → SSub (suc n) n
(t forᵏ α) β = maybe′ svar t (thick α β)

for-hitᵏ : ∀ {n} → (t : Skel n) → (α : Fin (suc n)) → (t forᵏ α) α ≡ t
for-hitᵏ t α = cong (maybe′ svar t) (thick-refl α)

for-missᵏ : ∀ {n} → (t : Skel n) → (α : Fin (suc n)) → (β : Fin n)
          → (t forᵏ α) (punchIn α β) ≡ svar β
for-missᵏ t α β = cong (maybe′ svar t) (thick-thin α β)

-- The occurrence check, combined with the renaming into the smaller
-- scope: a skeleton in which the variable does not occur is one of
-- the scope with the variable removed.

checkᵏ : ∀ {n} → Fin (suc n) → Skel (suc n) → Maybe (Skel n)
checkᵏ α (svar β)  = mmap svar (thick α β)
checkᵏ α (sBase b) = just (sBase b)
checkᵏ α sUnit     = just sUnit
checkᵏ α sBool     = just sBool
checkᵏ α (t s× u)  = zip₂ _s×_ (checkᵏ α t) (checkᵏ α u)
checkᵏ α sEmpty    = just sEmpty
checkᵏ α (t s⇒ u)  = zip₂ _s⇒_ (checkᵏ α t) (checkᵏ α u)
checkᵏ α (sBox t)  = mmap sBox_ (checkᵏ α t)
