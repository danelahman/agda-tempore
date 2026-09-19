------------------------------------------------------------------
-- Substitutions of the mirrored language                        --
--                                                               --
-- A substitution maps the three sorts of variables of one scope --
-- to open types, resource expressions, and effect expressions   --
-- over another scope. Its action on contexts preserves the      --
-- number of bound variables, so no transports occur anywhere.   --
------------------------------------------------------------------

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import TypeInference.Scopes

module TypeInference.Open.Subst (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Syntax.Types S

open import TypeInference.Open.Grades   S
open import TypeInference.Open.Types    S
open import TypeInference.Open.Contexts S

-- Substitutions

record Subst (Θ Θ' : Scope) : Set where
  constructor sub
  field
    sTy : TyVar Θ → OVType Θ'              -- type variables to open types
    sR  : RVar Θ → RExp Θ'                 -- resource-grade variables
    sE  : EVar Θ → EExp Θ'                 -- effect-grade variables

open Subst public

-- Action of a substitution on the four syntactic categories

infixl 50 _[_]ᵉ _[_]ʳ _[_]ᵛ _[_]ᶜ _[_]ᶜᵗˣ

_[_]ᵉ : ∀ {Θ Θ'} → EExp Θ → Subst Θ Θ' → EExp Θ'
evar i    [ σ ]ᵉ = sE σ i
econst ε  [ σ ]ᵉ = econst ε
(ε ·̂ₑ ε') [ σ ]ᵉ = ε [ σ ]ᵉ ·̂ₑ ε' [ σ ]ᵉ

_[_]ʳ : ∀ {Θ Θ'} → RExp Θ → Subst Θ Θ' → RExp Θ'
rvar i    [ σ ]ʳ = sR σ i
rconst ρ  [ σ ]ʳ = rconst ρ
(ρ ·̂ᵣ ρ') [ σ ]ʳ = ρ [ σ ]ʳ ·̂ᵣ ρ' [ σ ]ʳ
∣ ε ∣̂ᵉ    [ σ ]ʳ = ∣ ε [ σ ]ᵉ ∣̂ᵉ

mutual

  _[_]ᵛ : ∀ {Θ Θ'} → OVType Θ → Subst Θ Θ' → OVType Θ'
  tvar α    [ σ ]ᵛ = sTy σ α
  Base b    [ σ ]ᵛ = Base b
  Unit      [ σ ]ᵛ = Unit
  Bool      [ σ ]ᵛ = Bool
  (A |×| B) [ σ ]ᵛ = A [ σ ]ᵛ |×| B [ σ ]ᵛ
  Empty     [ σ ]ᵛ = Empty
  (A ⇒ C)   [ σ ]ᵛ = A [ σ ]ᵛ ⇒ C [ σ ]ᶜ
  ([ ρ ] A) [ σ ]ᵛ = [ ρ [ σ ]ʳ ] A [ σ ]ᵛ

  _[_]ᶜ : ∀ {Θ Θ'} → OCType Θ → Subst Θ Θ' → OCType Θ'
  (A ‼ ε) [ σ ]ᶜ = A [ σ ]ᵛ ‼ ε [ σ ]ᵉ

_[_]ᶜᵗˣ : ∀ {Θ Θ' n} → OCtx Θ n → Subst Θ Θ' → OCtx Θ' n
[]        [ σ ]ᶜᵗˣ = []
(Γ ∷ A)   [ σ ]ᶜᵗˣ = Γ [ σ ]ᶜᵗˣ ∷ A [ σ ]ᵛ
(Γ ⟨ ρ ⟩) [ σ ]ᶜᵗˣ = Γ [ σ ]ᶜᵗˣ ⟨ ρ [ σ ]ʳ ⟩

-- Identity and composition (apply the first, then substitute with the second)

infixl 25 _⨟ˢ_

idˢ : ∀ {Θ} → Subst Θ Θ
idˢ = sub tvar rvar evar

_⨟ˢ_ : ∀ {Θ Θ' Θ''} → Subst Θ Θ' → Subst Θ' Θ'' → Subst Θ Θ''
σ ⨟ˢ δ = sub (λ α → sTy σ α [ δ ]ᵛ)
             (λ i → sR σ i [ δ ]ʳ)
             (λ i → sE σ i [ δ ]ᵉ)

-- Weakening substitutions: every variable goes to its injected self

wkˢᵗ : ∀ {Θ} → Subst Θ (Θ +ty)
wkˢᵗ {Θ} = sub (λ α → tvar (wkᵗ-tv Θ α))
               (λ i → rvar (wkᵗ-rv Θ i))
               (λ i → evar (wkᵗ-ev Θ i))

wkˢʳ : ∀ {Θ} → Subst Θ (Θ +r)
wkˢʳ {Θ} = sub (λ α → tvar (wkʳ-tv Θ α))
               (λ i → rvar (wkʳ-rv Θ i))
               (λ i → evar (wkʳ-ev Θ i))

wkˢᵉ : ∀ {Θ} → Subst Θ (Θ +e)
wkˢᵉ {Θ} = sub (λ α → tvar (wkᵉ-tv Θ α))
               (λ i → rvar (wkᵉ-rv Θ i))
               (λ i → evar (wkᵉ-ev Θ i))

-- Lifting a substitution over a newly bound variable.
-- The target scope is named in the `zero` clauses: `newᵗ` and friends
-- do not determine it (`TyVar` is `Fin` of a projection).

infixl 32 _↑ᵗ _↑ʳ _↑ᵉ

_↑ᵗ : ∀ {Θ Θ'} → Subst Θ Θ' → Subst (Θ +ty) (Θ' +ty)
sTy (_↑ᵗ {Θ' = Θ'} σ) zero    = tvar (newᵗ {Θ'})
sTy (σ ↑ᵗ)            (suc α) = wkᵗ-v (sTy σ α)
sR  (σ ↑ᵗ)            i       = wkᵗ-r (sR σ i)
sE  (σ ↑ᵗ)            i       = wkᵗ-e (sE σ i)

_↑ʳ : ∀ {Θ Θ'} → Subst Θ Θ' → Subst (Θ +r) (Θ' +r)
sTy (σ ↑ʳ)            α       = wkʳ-v (sTy σ α)
sR  (_↑ʳ {Θ' = Θ'} σ) zero    = rvar (newʳ {Θ'})
sR  (σ ↑ʳ)            (suc i) = wkʳ-r (sR σ i)
sE  (σ ↑ʳ)            i       = wkʳ-e (sE σ i)

_↑ᵉ : ∀ {Θ Θ'} → Subst Θ Θ' → Subst (Θ +e) (Θ' +e)
sTy (σ ↑ᵉ)            α       = wkᵉ-v (sTy σ α)
sR  (σ ↑ᵉ)            i       = wkᵉ-r (sR σ i)
sE  (_↑ᵉ {Θ' = Θ'} σ) zero    = evar (newᵉ {Θ'})
sE  (σ ↑ᵉ)            (suc i) = wkᵉ-e (sE σ i)

-- Extending a substitution: the newly bound variable goes to the given image

infixl 28 _,ᵗ_ _,ʳ_ _,ᵉ_

_,ᵗ_ : ∀ {Θ Θ'} → Subst Θ Θ' → OVType Θ' → Subst (Θ +ty) Θ'
sTy (σ ,ᵗ B) zero    = B
sTy (σ ,ᵗ B) (suc α) = sTy σ α
sR  (σ ,ᵗ B) i       = sR σ i
sE  (σ ,ᵗ B) i       = sE σ i

_,ʳ_ : ∀ {Θ Θ'} → Subst Θ Θ' → RExp Θ' → Subst (Θ +r) Θ'
sTy (σ ,ʳ ρ) α       = sTy σ α
sR  (σ ,ʳ ρ) zero    = ρ
sR  (σ ,ʳ ρ) (suc i) = sR σ i
sE  (σ ,ʳ ρ) i       = sE σ i

_,ᵉ_ : ∀ {Θ Θ'} → Subst Θ Θ' → EExp Θ' → Subst (Θ +e) Θ'
sTy (σ ,ᵉ ε) α       = sTy σ α
sR  (σ ,ᵉ ε) i       = sR σ i
sE  (σ ,ᵉ ε) zero    = ε
sE  (σ ,ᵉ ε) (suc i) = sE σ i

-- Pointwise equality of substitutions (avoids function extensionality)

infix 20 _≐ˢ_

record _≐ˢ_ {Θ Θ'} (σ δ : Subst Θ Θ') : Set where
  constructor mk≐ˢ
  field
    ≐ᵗ : (α : TyVar Θ) → sTy σ α ≡ sTy δ α
    ≐ʳ : (i : RVar Θ) → sR σ i ≡ sR δ i
    ≐ᵉ : (i : EVar Θ) → sE σ i ≡ sE δ i

open _≐ˢ_ public

[id]ᵉ : ∀ {Θ} → (ε : EExp Θ) → ε [ idˢ ]ᵉ ≡ ε
[id]ᵉ (evar i)   = refl
[id]ᵉ (econst ε) = refl
[id]ᵉ (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ ([id]ᵉ ε) ([id]ᵉ ε')

[id]ʳ : ∀ {Θ} → (ρ : RExp Θ) → ρ [ idˢ ]ʳ ≡ ρ
[id]ʳ (rvar i)   = refl
[id]ʳ (rconst ρ) = refl
[id]ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ ([id]ʳ ρ) ([id]ʳ ρ')
[id]ʳ ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ ([id]ᵉ ε)

mutual

  [id]ᵛ : ∀ {Θ} → (A : OVType Θ) → A [ idˢ ]ᵛ ≡ A
  [id]ᵛ (tvar α)  = refl
  [id]ᵛ (Base b)  = refl
  [id]ᵛ Unit      = refl
  [id]ᵛ Bool      = refl
  [id]ᵛ (A |×| B) = cong₂ _|×|_ ([id]ᵛ A) ([id]ᵛ B)
  [id]ᵛ Empty     = refl
  [id]ᵛ (A ⇒ C)   = cong₂ _⇒_ ([id]ᵛ A) ([id]ᶜ C)
  [id]ᵛ ([ ρ ] A) = cong₂ [_]_ ([id]ʳ ρ) ([id]ᵛ A)

  [id]ᶜ : ∀ {Θ} → (C : OCType Θ) → C [ idˢ ]ᶜ ≡ C
  [id]ᶜ (A ‼ ε) = cong₂ _‼_ ([id]ᵛ A) ([id]ᵉ ε)

[id]ᶜᵗˣ : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ idˢ ]ᶜᵗˣ ≡ Γ
[id]ᶜᵗˣ []        = refl
[id]ᶜᵗˣ (Γ ∷ A)   = cong₂ _∷_ ([id]ᶜᵗˣ Γ) ([id]ᵛ A)
[id]ᶜᵗˣ (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ ([id]ᶜᵗˣ Γ) ([id]ʳ ρ)

[⨟]ᵉ : ∀ {Θ Θ' Θ''} → (ε : EExp Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
     → ε [ σ ]ᵉ [ δ ]ᵉ ≡ ε [ σ ⨟ˢ δ ]ᵉ
[⨟]ᵉ (evar i)   σ δ = refl
[⨟]ᵉ (econst ε) σ δ = refl
[⨟]ᵉ (ε ·̂ₑ ε')  σ δ = cong₂ _·̂ₑ_ ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)

[⨟]ʳ : ∀ {Θ Θ' Θ''} → (ρ : RExp Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
     → ρ [ σ ]ʳ [ δ ]ʳ ≡ ρ [ σ ⨟ˢ δ ]ʳ
[⨟]ʳ (rvar i)   σ δ = refl
[⨟]ʳ (rconst ρ) σ δ = refl
[⨟]ʳ (ρ ·̂ᵣ ρ')  σ δ = cong₂ _·̂ᵣ_ ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
[⨟]ʳ ∣ ε ∣̂ᵉ     σ δ = cong ∣_∣̂ᵉ ([⨟]ᵉ ε σ δ)

mutual

  [⨟]ᵛ : ∀ {Θ Θ' Θ''} → (A : OVType Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → A [ σ ]ᵛ [ δ ]ᵛ ≡ A [ σ ⨟ˢ δ ]ᵛ
  [⨟]ᵛ (tvar α)  σ δ = refl
  [⨟]ᵛ (Base b)  σ δ = refl
  [⨟]ᵛ Unit      σ δ = refl
  [⨟]ᵛ Bool      σ δ = refl
  [⨟]ᵛ (A |×| B) σ δ = cong₂ _|×|_ ([⨟]ᵛ A σ δ) ([⨟]ᵛ B σ δ)
  [⨟]ᵛ Empty     σ δ = refl
  [⨟]ᵛ (A ⇒ C)   σ δ = cong₂ _⇒_ ([⨟]ᵛ A σ δ) ([⨟]ᶜ C σ δ)
  [⨟]ᵛ ([ ρ ] A) σ δ = cong₂ [_]_ ([⨟]ʳ ρ σ δ) ([⨟]ᵛ A σ δ)

  [⨟]ᶜ : ∀ {Θ Θ' Θ''} → (C : OCType Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → C [ σ ]ᶜ [ δ ]ᶜ ≡ C [ σ ⨟ˢ δ ]ᶜ
  [⨟]ᶜ (A ‼ ε) σ δ = cong₂ _‼_ ([⨟]ᵛ A σ δ) ([⨟]ᵉ ε σ δ)

[⨟]ᶜᵗˣ : ∀ {Θ Θ' Θ'' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → Γ [ σ ]ᶜᵗˣ [ δ ]ᶜᵗˣ ≡ Γ [ σ ⨟ˢ δ ]ᶜᵗˣ
[⨟]ᶜᵗˣ []        σ δ = refl
[⨟]ᶜᵗˣ (Γ ∷ A)   σ δ = cong₂ _∷_ ([⨟]ᶜᵗˣ Γ σ δ) ([⨟]ᵛ A σ δ)
[⨟]ᶜᵗˣ (Γ ⟨ ρ ⟩) σ δ = cong₂ _⟨_⟩ ([⨟]ᶜᵗˣ Γ σ δ) ([⨟]ʳ ρ σ δ)

[≐]ᵉ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (ε : EExp Θ) → ε [ σ ]ᵉ ≡ ε [ δ ]ᵉ
[≐]ᵉ p (evar i)   = ≐ᵉ p i
[≐]ᵉ p (econst ε) = refl
[≐]ᵉ p (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ ([≐]ᵉ p ε) ([≐]ᵉ p ε')

[≐]ʳ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (ρ : RExp Θ) → ρ [ σ ]ʳ ≡ ρ [ δ ]ʳ
[≐]ʳ p (rvar i)   = ≐ʳ p i
[≐]ʳ p (rconst ρ) = refl
[≐]ʳ p (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ ([≐]ʳ p ρ) ([≐]ʳ p ρ')
[≐]ʳ p ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ ([≐]ᵉ p ε)

mutual

  [≐]ᵛ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (A : OVType Θ) → A [ σ ]ᵛ ≡ A [ δ ]ᵛ
  [≐]ᵛ p (tvar α)  = ≐ᵗ p α
  [≐]ᵛ p (Base b)  = refl
  [≐]ᵛ p Unit      = refl
  [≐]ᵛ p Bool      = refl
  [≐]ᵛ p (A |×| B) = cong₂ _|×|_ ([≐]ᵛ p A) ([≐]ᵛ p B)
  [≐]ᵛ p Empty     = refl
  [≐]ᵛ p (A ⇒ C)   = cong₂ _⇒_ ([≐]ᵛ p A) ([≐]ᶜ p C)
  [≐]ᵛ p ([ ρ ] A) = cong₂ [_]_ ([≐]ʳ p ρ) ([≐]ᵛ p A)

  [≐]ᶜ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (C : OCType Θ) → C [ σ ]ᶜ ≡ C [ δ ]ᶜ
  [≐]ᶜ p (A ‼ ε) = cong₂ _‼_ ([≐]ᵛ p A) ([≐]ᵉ p ε)

[≐]ᶜᵗˣ : ∀ {Θ Θ' n} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (Γ : OCtx Θ n)
       → Γ [ σ ]ᶜᵗˣ ≡ Γ [ δ ]ᶜᵗˣ
[≐]ᶜᵗˣ p []        = refl
[≐]ᶜᵗˣ p (Γ ∷ A)   = cong₂ _∷_ ([≐]ᶜᵗˣ p Γ) ([≐]ᵛ p A)
[≐]ᶜᵗˣ p (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ ([≐]ᶜᵗˣ p Γ) ([≐]ʳ p ρ)

wkˢᵗ-e : ∀ {Θ} → (ε : EExp Θ) → ε [ wkˢᵗ ]ᵉ ≡ wkᵗ-e ε
wkˢᵗ-e (evar i)   = refl
wkˢᵗ-e (econst ε) = refl
wkˢᵗ-e (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (wkˢᵗ-e ε) (wkˢᵗ-e ε')

wkˢʳ-e : ∀ {Θ} → (ε : EExp Θ) → ε [ wkˢʳ ]ᵉ ≡ wkʳ-e ε
wkˢʳ-e (evar i)   = refl
wkˢʳ-e (econst ε) = refl
wkˢʳ-e (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (wkˢʳ-e ε) (wkˢʳ-e ε')

wkˢᵉ-e : ∀ {Θ} → (ε : EExp Θ) → ε [ wkˢᵉ ]ᵉ ≡ wkᵉ-e ε
wkˢᵉ-e (evar i)   = refl
wkˢᵉ-e (econst ε) = refl
wkˢᵉ-e (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (wkˢᵉ-e ε) (wkˢᵉ-e ε')

wkˢᵗ-r : ∀ {Θ} → (ρ : RExp Θ) → ρ [ wkˢᵗ ]ʳ ≡ wkᵗ-r ρ
wkˢᵗ-r (rvar i)   = refl
wkˢᵗ-r (rconst ρ) = refl
wkˢᵗ-r (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (wkˢᵗ-r ρ) (wkˢᵗ-r ρ')
wkˢᵗ-r ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (wkˢᵗ-e ε)

wkˢʳ-r : ∀ {Θ} → (ρ : RExp Θ) → ρ [ wkˢʳ ]ʳ ≡ wkʳ-r ρ
wkˢʳ-r (rvar i)   = refl
wkˢʳ-r (rconst ρ) = refl
wkˢʳ-r (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (wkˢʳ-r ρ) (wkˢʳ-r ρ')
wkˢʳ-r ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (wkˢʳ-e ε)

wkˢᵉ-r : ∀ {Θ} → (ρ : RExp Θ) → ρ [ wkˢᵉ ]ʳ ≡ wkᵉ-r ρ
wkˢᵉ-r (rvar i)   = refl
wkˢᵉ-r (rconst ρ) = refl
wkˢᵉ-r (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (wkˢᵉ-r ρ) (wkˢᵉ-r ρ')
wkˢᵉ-r ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (wkˢᵉ-e ε)

mutual

  wkˢᵗ-v : ∀ {Θ} → (A : OVType Θ) → A [ wkˢᵗ ]ᵛ ≡ wkᵗ-v A
  wkˢᵗ-v (tvar α)  = refl
  wkˢᵗ-v (Base b)  = refl
  wkˢᵗ-v Unit      = refl
  wkˢᵗ-v Bool      = refl
  wkˢᵗ-v (A |×| B) = cong₂ _|×|_ (wkˢᵗ-v A) (wkˢᵗ-v B)
  wkˢᵗ-v Empty     = refl
  wkˢᵗ-v (A ⇒ C)   = cong₂ _⇒_ (wkˢᵗ-v A) (wkˢᵗ-c C)
  wkˢᵗ-v ([ ρ ] A) = cong₂ [_]_ (wkˢᵗ-r ρ) (wkˢᵗ-v A)

  wkˢᵗ-c : ∀ {Θ} → (C : OCType Θ) → C [ wkˢᵗ ]ᶜ ≡ wkᵗ-c C
  wkˢᵗ-c (A ‼ ε) = cong₂ _‼_ (wkˢᵗ-v A) (wkˢᵗ-e ε)

mutual

  wkˢʳ-v : ∀ {Θ} → (A : OVType Θ) → A [ wkˢʳ ]ᵛ ≡ wkʳ-v A
  wkˢʳ-v (tvar α)  = refl
  wkˢʳ-v (Base b)  = refl
  wkˢʳ-v Unit      = refl
  wkˢʳ-v Bool      = refl
  wkˢʳ-v (A |×| B) = cong₂ _|×|_ (wkˢʳ-v A) (wkˢʳ-v B)
  wkˢʳ-v Empty     = refl
  wkˢʳ-v (A ⇒ C)   = cong₂ _⇒_ (wkˢʳ-v A) (wkˢʳ-c C)
  wkˢʳ-v ([ ρ ] A) = cong₂ [_]_ (wkˢʳ-r ρ) (wkˢʳ-v A)

  wkˢʳ-c : ∀ {Θ} → (C : OCType Θ) → C [ wkˢʳ ]ᶜ ≡ wkʳ-c C
  wkˢʳ-c (A ‼ ε) = cong₂ _‼_ (wkˢʳ-v A) (wkˢʳ-e ε)

mutual

  wkˢᵉ-v : ∀ {Θ} → (A : OVType Θ) → A [ wkˢᵉ ]ᵛ ≡ wkᵉ-v A
  wkˢᵉ-v (tvar α)  = refl
  wkˢᵉ-v (Base b)  = refl
  wkˢᵉ-v Unit      = refl
  wkˢᵉ-v Bool      = refl
  wkˢᵉ-v (A |×| B) = cong₂ _|×|_ (wkˢᵉ-v A) (wkˢᵉ-v B)
  wkˢᵉ-v Empty     = refl
  wkˢᵉ-v (A ⇒ C)   = cong₂ _⇒_ (wkˢᵉ-v A) (wkˢᵉ-c C)
  wkˢᵉ-v ([ ρ ] A) = cong₂ [_]_ (wkˢᵉ-r ρ) (wkˢᵉ-v A)

  wkˢᵉ-c : ∀ {Θ} → (C : OCType Θ) → C [ wkˢᵉ ]ᶜ ≡ wkᵉ-c C
  wkˢᵉ-c (A ‼ ε) = cong₂ _‼_ (wkˢᵉ-v A) (wkˢᵉ-e ε)

wkˢᵗ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ wkˢᵗ ]ᶜᵗˣ ≡ wkᵗ-ctx Γ
wkˢᵗ-ctx []        = refl
wkˢᵗ-ctx (Γ ∷ A)   = cong₂ _∷_ (wkˢᵗ-ctx Γ) (wkˢᵗ-v A)
wkˢᵗ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (wkˢᵗ-ctx Γ) (wkˢᵗ-r ρ)

wkˢʳ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ wkˢʳ ]ᶜᵗˣ ≡ wkʳ-ctx Γ
wkˢʳ-ctx []        = refl
wkˢʳ-ctx (Γ ∷ A)   = cong₂ _∷_ (wkˢʳ-ctx Γ) (wkˢʳ-v A)
wkˢʳ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (wkˢʳ-ctx Γ) (wkˢʳ-r ρ)

wkˢᵉ-ctx : ∀ {Θ n} → (Γ : OCtx Θ n) → Γ [ wkˢᵉ ]ᶜᵗˣ ≡ wkᵉ-ctx Γ
wkˢᵉ-ctx []        = refl
wkˢᵉ-ctx (Γ ∷ A)   = cong₂ _∷_ (wkˢᵉ-ctx Γ) (wkˢᵉ-v A)
wkˢᵉ-ctx (Γ ⟨ ρ ⟩) = cong₂ _⟨_⟩ (wkˢᵉ-ctx Γ) (wkˢᵉ-r ρ)

wkˢᵗ-,ᵗ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → wkˢᵗ ⨟ˢ (σ ,ᵗ B) ≐ˢ σ
wkˢᵗ-,ᵗ σ B = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wkˢʳ-,ʳ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ : RExp Θ') → wkˢʳ ⨟ˢ (σ ,ʳ ρ) ≐ˢ σ
wkˢʳ-,ʳ σ ρ = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wkˢᵉ-,ᵉ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε : EExp Θ') → wkˢᵉ ⨟ˢ (σ ,ᵉ ε) ≐ˢ σ
wkˢᵉ-,ᵉ σ ε = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

wkˢᵗ-↑ᵗ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → wkˢᵗ ⨟ˢ (σ ↑ᵗ) ≐ˢ σ ⨟ˢ wkˢᵗ
wkˢᵗ-↑ᵗ σ = mk≐ˢ (λ α → sym (wkˢᵗ-v (sTy σ α)))
                 (λ i → sym (wkˢᵗ-r (sR σ i)))
                 (λ i → sym (wkˢᵗ-e (sE σ i)))

wkˢʳ-↑ʳ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → wkˢʳ ⨟ˢ (σ ↑ʳ) ≐ˢ σ ⨟ˢ wkˢʳ
wkˢʳ-↑ʳ σ = mk≐ˢ (λ α → sym (wkˢʳ-v (sTy σ α)))
                 (λ i → sym (wkˢʳ-r (sR σ i)))
                 (λ i → sym (wkˢʳ-e (sE σ i)))

wkˢᵉ-↑ᵉ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → wkˢᵉ ⨟ˢ (σ ↑ᵉ) ≐ˢ σ ⨟ˢ wkˢᵉ
wkˢᵉ-↑ᵉ σ = mk≐ˢ (λ α → sym (wkˢᵉ-v (sTy σ α)))
                 (λ i → sym (wkˢᵉ-r (sR σ i)))
                 (λ i → sym (wkˢᵉ-e (sE σ i)))

-- `wk-,`: an extension undoes a weakening.

wk-,ᵗ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ε : EExp Θ)
        → wkᵗ-e ε [ σ ,ᵗ B ]ᵉ ≡ ε [ σ ]ᵉ
wk-,ᵗ-e σ B ε = trans (cong (_[ σ ,ᵗ B ]ᵉ) (sym (wkˢᵗ-e ε)))
                (trans ([⨟]ᵉ ε wkˢᵗ (σ ,ᵗ B)) ([≐]ᵉ (wkˢᵗ-,ᵗ σ B) ε))

wk-,ᵗ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (ρ : RExp Θ)
        → wkᵗ-r ρ [ σ ,ᵗ B ]ʳ ≡ ρ [ σ ]ʳ
wk-,ᵗ-r σ B ρ = trans (cong (_[ σ ,ᵗ B ]ʳ) (sym (wkˢᵗ-r ρ)))
                (trans ([⨟]ʳ ρ wkˢᵗ (σ ,ᵗ B)) ([≐]ʳ (wkˢᵗ-,ᵗ σ B) ρ))

wk-,ᵗ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (A : OVType Θ)
        → wkᵗ-v A [ σ ,ᵗ B ]ᵛ ≡ A [ σ ]ᵛ
wk-,ᵗ-v σ B A = trans (cong (_[ σ ,ᵗ B ]ᵛ) (sym (wkˢᵗ-v A)))
                (trans ([⨟]ᵛ A wkˢᵗ (σ ,ᵗ B)) ([≐]ᵛ (wkˢᵗ-,ᵗ σ B) A))

wk-,ᵗ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (B : OVType Θ') → (C : OCType Θ)
        → wkᵗ-c C [ σ ,ᵗ B ]ᶜ ≡ C [ σ ]ᶜ
wk-,ᵗ-c σ B C = trans (cong (_[ σ ,ᵗ B ]ᶜ) (sym (wkˢᵗ-c C)))
                (trans ([⨟]ᶜ C wkˢᵗ (σ ,ᵗ B)) ([≐]ᶜ (wkˢᵗ-,ᵗ σ B) C))

wk-,ᵗ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (B : OVType Θ') → (Γ : OCtx Θ n)
          → wkᵗ-ctx Γ [ σ ,ᵗ B ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
wk-,ᵗ-ctx σ B Γ = trans (cong (_[ σ ,ᵗ B ]ᶜᵗˣ) (sym (wkˢᵗ-ctx Γ)))
                  (trans ([⨟]ᶜᵗˣ Γ wkˢᵗ (σ ,ᵗ B)) ([≐]ᶜᵗˣ (wkˢᵗ-,ᵗ σ B) Γ))

wk-,ʳ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ' : RExp Θ') → (ε : EExp Θ)
        → wkʳ-e ε [ σ ,ʳ ρ' ]ᵉ ≡ ε [ σ ]ᵉ
wk-,ʳ-e σ ρ' ε = trans (cong (_[ σ ,ʳ ρ' ]ᵉ) (sym (wkˢʳ-e ε)))
                 (trans ([⨟]ᵉ ε wkˢʳ (σ ,ʳ ρ')) ([≐]ᵉ (wkˢʳ-,ʳ σ ρ') ε))

wk-,ʳ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ' : RExp Θ') → (ρ : RExp Θ)
        → wkʳ-r ρ [ σ ,ʳ ρ' ]ʳ ≡ ρ [ σ ]ʳ
wk-,ʳ-r σ ρ' ρ = trans (cong (_[ σ ,ʳ ρ' ]ʳ) (sym (wkˢʳ-r ρ)))
                 (trans ([⨟]ʳ ρ wkˢʳ (σ ,ʳ ρ')) ([≐]ʳ (wkˢʳ-,ʳ σ ρ') ρ))

wk-,ʳ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ' : RExp Θ') → (A : OVType Θ)
        → wkʳ-v A [ σ ,ʳ ρ' ]ᵛ ≡ A [ σ ]ᵛ
wk-,ʳ-v σ ρ' A = trans (cong (_[ σ ,ʳ ρ' ]ᵛ) (sym (wkˢʳ-v A)))
                 (trans ([⨟]ᵛ A wkˢʳ (σ ,ʳ ρ')) ([≐]ᵛ (wkˢʳ-,ʳ σ ρ') A))

wk-,ʳ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ' : RExp Θ') → (C : OCType Θ)
        → wkʳ-c C [ σ ,ʳ ρ' ]ᶜ ≡ C [ σ ]ᶜ
wk-,ʳ-c σ ρ' C = trans (cong (_[ σ ,ʳ ρ' ]ᶜ) (sym (wkˢʳ-c C)))
                 (trans ([⨟]ᶜ C wkˢʳ (σ ,ʳ ρ')) ([≐]ᶜ (wkˢʳ-,ʳ σ ρ') C))

wk-,ʳ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (ρ' : RExp Θ') → (Γ : OCtx Θ n)
          → wkʳ-ctx Γ [ σ ,ʳ ρ' ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
wk-,ʳ-ctx σ ρ' Γ = trans (cong (_[ σ ,ʳ ρ' ]ᶜᵗˣ) (sym (wkˢʳ-ctx Γ)))
                   (trans ([⨟]ᶜᵗˣ Γ wkˢʳ (σ ,ʳ ρ')) ([≐]ᶜᵗˣ (wkˢʳ-,ʳ σ ρ') Γ))

wk-,ᵉ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε' : EExp Θ') → (ε : EExp Θ)
        → wkᵉ-e ε [ σ ,ᵉ ε' ]ᵉ ≡ ε [ σ ]ᵉ
wk-,ᵉ-e σ ε' ε = trans (cong (_[ σ ,ᵉ ε' ]ᵉ) (sym (wkˢᵉ-e ε)))
                 (trans ([⨟]ᵉ ε wkˢᵉ (σ ,ᵉ ε')) ([≐]ᵉ (wkˢᵉ-,ᵉ σ ε') ε))

wk-,ᵉ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε' : EExp Θ') → (ρ : RExp Θ)
        → wkᵉ-r ρ [ σ ,ᵉ ε' ]ʳ ≡ ρ [ σ ]ʳ
wk-,ᵉ-r σ ε' ρ = trans (cong (_[ σ ,ᵉ ε' ]ʳ) (sym (wkˢᵉ-r ρ)))
                 (trans ([⨟]ʳ ρ wkˢᵉ (σ ,ᵉ ε')) ([≐]ʳ (wkˢᵉ-,ᵉ σ ε') ρ))

wk-,ᵉ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε' : EExp Θ') → (A : OVType Θ)
        → wkᵉ-v A [ σ ,ᵉ ε' ]ᵛ ≡ A [ σ ]ᵛ
wk-,ᵉ-v σ ε' A = trans (cong (_[ σ ,ᵉ ε' ]ᵛ) (sym (wkˢᵉ-v A)))
                 (trans ([⨟]ᵛ A wkˢᵉ (σ ,ᵉ ε')) ([≐]ᵛ (wkˢᵉ-,ᵉ σ ε') A))

wk-,ᵉ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε' : EExp Θ') → (C : OCType Θ)
        → wkᵉ-c C [ σ ,ᵉ ε' ]ᶜ ≡ C [ σ ]ᶜ
wk-,ᵉ-c σ ε' C = trans (cong (_[ σ ,ᵉ ε' ]ᶜ) (sym (wkˢᵉ-c C)))
                 (trans ([⨟]ᶜ C wkˢᵉ (σ ,ᵉ ε')) ([≐]ᶜ (wkˢᵉ-,ᵉ σ ε') C))

wk-,ᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (ε' : EExp Θ') → (Γ : OCtx Θ n)
          → wkᵉ-ctx Γ [ σ ,ᵉ ε' ]ᶜᵗˣ ≡ Γ [ σ ]ᶜᵗˣ
wk-,ᵉ-ctx σ ε' Γ = trans (cong (_[ σ ,ᵉ ε' ]ᶜᵗˣ) (sym (wkˢᵉ-ctx Γ)))
                   (trans ([⨟]ᶜᵗˣ Γ wkˢᵉ (σ ,ᵉ ε')) ([≐]ᶜᵗˣ (wkˢᵉ-,ᵉ σ ε') Γ))

-- `wk-↑`: a lift commutes with a weakening.

wk-↑ᵗ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε : EExp Θ)
        → wkᵗ-e ε [ σ ↑ᵗ ]ᵉ ≡ wkᵗ-e (ε [ σ ]ᵉ)
wk-↑ᵗ-e σ ε = trans (cong (_[ σ ↑ᵗ ]ᵉ) (sym (wkˢᵗ-e ε)))
              (trans ([⨟]ᵉ ε wkˢᵗ (σ ↑ᵗ))
              (trans ([≐]ᵉ (wkˢᵗ-↑ᵗ σ) ε)
              (trans (sym ([⨟]ᵉ ε σ wkˢᵗ)) (wkˢᵗ-e (ε [ σ ]ᵉ)))))

wk-↑ᵗ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ : RExp Θ)
        → wkᵗ-r ρ [ σ ↑ᵗ ]ʳ ≡ wkᵗ-r (ρ [ σ ]ʳ)
wk-↑ᵗ-r σ ρ = trans (cong (_[ σ ↑ᵗ ]ʳ) (sym (wkˢᵗ-r ρ)))
              (trans ([⨟]ʳ ρ wkˢᵗ (σ ↑ᵗ))
              (trans ([≐]ʳ (wkˢᵗ-↑ᵗ σ) ρ)
              (trans (sym ([⨟]ʳ ρ σ wkˢᵗ)) (wkˢᵗ-r (ρ [ σ ]ʳ)))))

wk-↑ᵗ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (A : OVType Θ)
        → wkᵗ-v A [ σ ↑ᵗ ]ᵛ ≡ wkᵗ-v (A [ σ ]ᵛ)
wk-↑ᵗ-v σ A = trans (cong (_[ σ ↑ᵗ ]ᵛ) (sym (wkˢᵗ-v A)))
              (trans ([⨟]ᵛ A wkˢᵗ (σ ↑ᵗ))
              (trans ([≐]ᵛ (wkˢᵗ-↑ᵗ σ) A)
              (trans (sym ([⨟]ᵛ A σ wkˢᵗ)) (wkˢᵗ-v (A [ σ ]ᵛ)))))

wk-↑ᵗ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (C : OCType Θ)
        → wkᵗ-c C [ σ ↑ᵗ ]ᶜ ≡ wkᵗ-c (C [ σ ]ᶜ)
wk-↑ᵗ-c σ C = trans (cong (_[ σ ↑ᵗ ]ᶜ) (sym (wkˢᵗ-c C)))
              (trans ([⨟]ᶜ C wkˢᵗ (σ ↑ᵗ))
              (trans ([≐]ᶜ (wkˢᵗ-↑ᵗ σ) C)
              (trans (sym ([⨟]ᶜ C σ wkˢᵗ)) (wkˢᵗ-c (C [ σ ]ᶜ)))))

wk-↑ᵗ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n)
          → wkᵗ-ctx Γ [ σ ↑ᵗ ]ᶜᵗˣ ≡ wkᵗ-ctx (Γ [ σ ]ᶜᵗˣ)
wk-↑ᵗ-ctx σ Γ = trans (cong (_[ σ ↑ᵗ ]ᶜᵗˣ) (sym (wkˢᵗ-ctx Γ)))
                (trans ([⨟]ᶜᵗˣ Γ wkˢᵗ (σ ↑ᵗ))
                (trans ([≐]ᶜᵗˣ (wkˢᵗ-↑ᵗ σ) Γ)
                (trans (sym ([⨟]ᶜᵗˣ Γ σ wkˢᵗ)) (wkˢᵗ-ctx (Γ [ σ ]ᶜᵗˣ)))))

wk-↑ʳ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε : EExp Θ)
        → wkʳ-e ε [ σ ↑ʳ ]ᵉ ≡ wkʳ-e (ε [ σ ]ᵉ)
wk-↑ʳ-e σ ε = trans (cong (_[ σ ↑ʳ ]ᵉ) (sym (wkˢʳ-e ε)))
              (trans ([⨟]ᵉ ε wkˢʳ (σ ↑ʳ))
              (trans ([≐]ᵉ (wkˢʳ-↑ʳ σ) ε)
              (trans (sym ([⨟]ᵉ ε σ wkˢʳ)) (wkˢʳ-e (ε [ σ ]ᵉ)))))

wk-↑ʳ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ : RExp Θ)
        → wkʳ-r ρ [ σ ↑ʳ ]ʳ ≡ wkʳ-r (ρ [ σ ]ʳ)
wk-↑ʳ-r σ ρ = trans (cong (_[ σ ↑ʳ ]ʳ) (sym (wkˢʳ-r ρ)))
              (trans ([⨟]ʳ ρ wkˢʳ (σ ↑ʳ))
              (trans ([≐]ʳ (wkˢʳ-↑ʳ σ) ρ)
              (trans (sym ([⨟]ʳ ρ σ wkˢʳ)) (wkˢʳ-r (ρ [ σ ]ʳ)))))

wk-↑ʳ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (A : OVType Θ)
        → wkʳ-v A [ σ ↑ʳ ]ᵛ ≡ wkʳ-v (A [ σ ]ᵛ)
wk-↑ʳ-v σ A = trans (cong (_[ σ ↑ʳ ]ᵛ) (sym (wkˢʳ-v A)))
              (trans ([⨟]ᵛ A wkˢʳ (σ ↑ʳ))
              (trans ([≐]ᵛ (wkˢʳ-↑ʳ σ) A)
              (trans (sym ([⨟]ᵛ A σ wkˢʳ)) (wkˢʳ-v (A [ σ ]ᵛ)))))

wk-↑ʳ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (C : OCType Θ)
        → wkʳ-c C [ σ ↑ʳ ]ᶜ ≡ wkʳ-c (C [ σ ]ᶜ)
wk-↑ʳ-c σ C = trans (cong (_[ σ ↑ʳ ]ᶜ) (sym (wkˢʳ-c C)))
              (trans ([⨟]ᶜ C wkˢʳ (σ ↑ʳ))
              (trans ([≐]ᶜ (wkˢʳ-↑ʳ σ) C)
              (trans (sym ([⨟]ᶜ C σ wkˢʳ)) (wkˢʳ-c (C [ σ ]ᶜ)))))

wk-↑ʳ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n)
          → wkʳ-ctx Γ [ σ ↑ʳ ]ᶜᵗˣ ≡ wkʳ-ctx (Γ [ σ ]ᶜᵗˣ)
wk-↑ʳ-ctx σ Γ = trans (cong (_[ σ ↑ʳ ]ᶜᵗˣ) (sym (wkˢʳ-ctx Γ)))
                (trans ([⨟]ᶜᵗˣ Γ wkˢʳ (σ ↑ʳ))
                (trans ([≐]ᶜᵗˣ (wkˢʳ-↑ʳ σ) Γ)
                (trans (sym ([⨟]ᶜᵗˣ Γ σ wkˢʳ)) (wkˢʳ-ctx (Γ [ σ ]ᶜᵗˣ)))))

wk-↑ᵉ-e : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ε : EExp Θ)
        → wkᵉ-e ε [ σ ↑ᵉ ]ᵉ ≡ wkᵉ-e (ε [ σ ]ᵉ)
wk-↑ᵉ-e σ ε = trans (cong (_[ σ ↑ᵉ ]ᵉ) (sym (wkˢᵉ-e ε)))
              (trans ([⨟]ᵉ ε wkˢᵉ (σ ↑ᵉ))
              (trans ([≐]ᵉ (wkˢᵉ-↑ᵉ σ) ε)
              (trans (sym ([⨟]ᵉ ε σ wkˢᵉ)) (wkˢᵉ-e (ε [ σ ]ᵉ)))))

wk-↑ᵉ-r : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (ρ : RExp Θ)
        → wkᵉ-r ρ [ σ ↑ᵉ ]ʳ ≡ wkᵉ-r (ρ [ σ ]ʳ)
wk-↑ᵉ-r σ ρ = trans (cong (_[ σ ↑ᵉ ]ʳ) (sym (wkˢᵉ-r ρ)))
              (trans ([⨟]ʳ ρ wkˢᵉ (σ ↑ᵉ))
              (trans ([≐]ʳ (wkˢᵉ-↑ᵉ σ) ρ)
              (trans (sym ([⨟]ʳ ρ σ wkˢᵉ)) (wkˢᵉ-r (ρ [ σ ]ʳ)))))

wk-↑ᵉ-v : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (A : OVType Θ)
        → wkᵉ-v A [ σ ↑ᵉ ]ᵛ ≡ wkᵉ-v (A [ σ ]ᵛ)
wk-↑ᵉ-v σ A = trans (cong (_[ σ ↑ᵉ ]ᵛ) (sym (wkˢᵉ-v A)))
              (trans ([⨟]ᵛ A wkˢᵉ (σ ↑ᵉ))
              (trans ([≐]ᵛ (wkˢᵉ-↑ᵉ σ) A)
              (trans (sym ([⨟]ᵛ A σ wkˢᵉ)) (wkˢᵉ-v (A [ σ ]ᵛ)))))

wk-↑ᵉ-c : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (C : OCType Θ)
        → wkᵉ-c C [ σ ↑ᵉ ]ᶜ ≡ wkᵉ-c (C [ σ ]ᶜ)
wk-↑ᵉ-c σ C = trans (cong (_[ σ ↑ᵉ ]ᶜ) (sym (wkˢᵉ-c C)))
              (trans ([⨟]ᶜ C wkˢᵉ (σ ↑ᵉ))
              (trans ([≐]ᶜ (wkˢᵉ-↑ᵉ σ) C)
              (trans (sym ([⨟]ᶜ C σ wkˢᵉ)) (wkˢᵉ-c (C [ σ ]ᶜ)))))

wk-↑ᵉ-ctx : ∀ {Θ Θ' n} → (σ : Subst Θ Θ') → (Γ : OCtx Θ n)
          → wkᵉ-ctx Γ [ σ ↑ᵉ ]ᶜᵗˣ ≡ wkᵉ-ctx (Γ [ σ ]ᶜᵗˣ)
wk-↑ᵉ-ctx σ Γ = trans (cong (_[ σ ↑ᵉ ]ᶜᵗˣ) (sym (wkˢᵉ-ctx Γ)))
                (trans ([⨟]ᶜᵗˣ Γ wkˢᵉ (σ ↑ᵉ))
                (trans ([≐]ᶜᵗˣ (wkˢᵉ-↑ᵉ σ) Γ)
                (trans (sym ([⨟]ᶜᵗˣ Γ σ wkˢᵉ)) (wkˢᵉ-ctx (Γ [ σ ]ᶜᵗˣ)))))

lookup-ty-subst : ∀ {Θ Θ' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → (i : Fin n)
                → lookup-ty (Γ [ σ ]ᶜᵗˣ) i ≡ lookup-ty Γ i [ σ ]ᵛ
lookup-ty-subst (Γ ∷ A)   σ zero    = refl
lookup-ty-subst (Γ ∷ A)   σ (suc i) = lookup-ty-subst Γ σ i
lookup-ty-subst (Γ ⟨ ρ ⟩) σ i       = lookup-ty-subst Γ σ i

lookup-gr-subst : ∀ {Θ Θ' n} → (Γ : OCtx Θ n) → (σ : Subst Θ Θ') → (i : Fin n)
                → lookup-gr (Γ [ σ ]ᶜᵗˣ) i ≡ lookup-gr Γ i [ σ ]ʳ
lookup-gr-subst (Γ ∷ A)   σ zero    = refl
lookup-gr-subst (Γ ∷ A)   σ (suc i) = lookup-gr-subst Γ σ i
lookup-gr-subst (Γ ⟨ ρ ⟩) σ i       = cong (_·̂ᵣ ρ [ σ ]ʳ) (lookup-gr-subst Γ σ i)

mutual

  ⌜⌝ᵛ-subst : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (A : VType) → ⌜ A ⌝ᵛ [ σ ]ᵛ ≡ ⌜ A ⌝ᵛ
  ⌜⌝ᵛ-subst σ (Base b)  = refl
  ⌜⌝ᵛ-subst σ Unit      = refl
  ⌜⌝ᵛ-subst σ Bool      = refl
  ⌜⌝ᵛ-subst σ (A |×| B) = cong₂ _|×|_ (⌜⌝ᵛ-subst σ A) (⌜⌝ᵛ-subst σ B)
  ⌜⌝ᵛ-subst σ Empty     = refl
  ⌜⌝ᵛ-subst σ (A ⇒ C)   = cong₂ _⇒_ (⌜⌝ᵛ-subst σ A) (⌜⌝ᶜ-subst σ C)
  ⌜⌝ᵛ-subst σ ([ ρ ] A) = cong₂ [_]_ refl (⌜⌝ᵛ-subst σ A)

  ⌜⌝ᶜ-subst : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (C : CType) → ⌜ C ⌝ᶜ [ σ ]ᶜ ≡ ⌜ C ⌝ᶜ
  ⌜⌝ᶜ-subst σ (A ‼ ε) = cong₂ _‼_ (⌜⌝ᵛ-subst σ A) refl

⌜⌝ᵍ-subst : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (A : GType) → ⌜ A ⌝ᵍ [ σ ]ᵛ ≡ ⌜ A ⌝ᵍ
⌜⌝ᵍ-subst σ (Base b)   = refl
⌜⌝ᵍ-subst σ Unit       = refl
⌜⌝ᵍ-subst σ Bool       = refl
⌜⌝ᵍ-subst σ Empty      = refl
⌜⌝ᵍ-subst σ (A |×|ᵍ B) = cong₂ _|×|_ (⌜⌝ᵍ-subst σ A) (⌜⌝ᵍ-subst σ B)
⌜⌝ᵍ-subst σ ([ ρ ]ᵍ A) = cong₂ [_]_ refl (⌜⌝ᵍ-subst σ A)
