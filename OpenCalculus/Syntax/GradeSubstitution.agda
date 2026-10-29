------------------------------------------------------------------
-- Substitutions of the open calculus                           --
--                                                              --
-- A substitution maps the three sorts of variables of one      --
-- scope to open types, resource expressions and effect         --
-- expressions over another scope. A scope extended by the      --
-- variables of another (`Θ ⊹ Ψ`) is substituted by a pair of   --
-- substitutions (`σ ⊕ˢ δ`).                                    --
------------------------------------------------------------------

open import Data.Bool.Base using (if_then_else_; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc; _↑ˡ_; _↑ʳ_)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Vec.Base using (Vec; tabulate) renaming (lookup to lookupᵛ)
open import Data.Vec.Properties using (lookup∘tabulate)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import OpenCalculus.Syntax.Scopes

module OpenCalculus.Syntax.GradeSubstitution (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Language.GroundTypes Grades BTs using (GType; Base; Unit; Bool; Nat; Empty; _|×|ᵍ_; _|+|ᵍ_; |List|ᵍ; [_]ᵍ_)

open import OpenCalculus.Syntax.Grades   S
open import OpenCalculus.Syntax.Types    S

-- Substitutions

record Subst (Θ Θ' : Scope) : Set where
  constructor sub
  field
    sTy : TyVar Θ → OVType Θ'              -- type variables to open types
    sR  : RVar Θ → RExp Θ'                 -- resource-grade variables
    sE  : EVar Θ → EExp Θ'                 -- effect-grade variables

open Subst public

-- Action of a substitution on the four syntactic categories

infixl 50 _[_]ᵉ _[_]ʳ _[_]ᵛ _[_]ᶜ

_[_]ᵉ : ∀ {Θ Θ'} → EExp Θ → Subst Θ Θ' → EExp Θ'
evar i    [ σ ]ᵉ = sE σ i
econst ε  [ σ ]ᵉ = econst ε
(ε ·̂ₑ ε') [ σ ]ᵉ = ε [ σ ]ᵉ ·̂ₑ ε' [ σ ]ᵉ
(ε ⊔̂ₑ ε') [ σ ]ᵉ = ε [ σ ]ᵉ ⊔̂ₑ ε' [ σ ]ᵉ

_[_]ʳ : ∀ {Θ Θ'} → RExp Θ → Subst Θ Θ' → RExp Θ'
rvar i    [ σ ]ʳ = sR σ i
rconst ρ  [ σ ]ʳ = rconst ρ
(ρ ·̂ᵣ ρ') [ σ ]ʳ = ρ [ σ ]ʳ ·̂ᵣ ρ' [ σ ]ʳ
(ρ ⊔̂ᵣ ρ') [ σ ]ʳ = ρ [ σ ]ʳ ⊔̂ᵣ ρ' [ σ ]ʳ
∣ ε ∣̂ᵉ    [ σ ]ʳ = ∣ ε [ σ ]ᵉ ∣̂ᵉ

mutual

  _[_]ᵛ : ∀ {Θ Θ'} → OVType Θ → Subst Θ Θ' → OVType Θ'
  tvar α    [ σ ]ᵛ = sTy σ α
  Base b    [ σ ]ᵛ = Base b
  Unit      [ σ ]ᵛ = Unit
  Bool      [ σ ]ᵛ = Bool
  Nat       [ σ ]ᵛ = Nat
  (A |×| B) [ σ ]ᵛ = A [ σ ]ᵛ |×| B [ σ ]ᵛ
  (A |+| B) [ σ ]ᵛ = A [ σ ]ᵛ |+| B [ σ ]ᵛ
  (|List| A) [ σ ]ᵛ = |List| (A [ σ ]ᵛ)
  Empty     [ σ ]ᵛ = Empty
  (A ⇒ C)   [ σ ]ᵛ = A [ σ ]ᵛ ⇒ C [ σ ]ᶜ
  (C ⇛ D)   [ σ ]ᵛ = C [ σ ]ᶜ ⇛ D [ σ ]ᶜ
  ([ ρ ] A) [ σ ]ᵛ = [ ρ [ σ ]ʳ ] A [ σ ]ᵛ

  _[_]ᶜ : ∀ {Θ Θ'} → OCType Θ → Subst Θ Θ' → OCType Θ'
  (A ‼ ε) [ σ ]ᶜ = A [ σ ]ᵛ ‼ ε [ σ ]ᵉ

-- Identity and composition (apply the first, then substitute with the second)

infixl 25 _⨟ˢ_

idˢ : ∀ {Θ} → Subst Θ Θ
idˢ = sub tvar rvar evar

_⨟ˢ_ : ∀ {Θ Θ' Θ''} → Subst Θ Θ' → Subst Θ' Θ'' → Subst Θ Θ''
σ ⨟ˢ δ = sub (λ α → sTy σ α [ δ ]ᵛ)
             (λ i → sR σ i [ δ ]ʳ)
             (λ i → sE σ i [ δ ]ᵉ)

-- A closed instance of any scope: type variables to `Unit`,
-- resource-grade variables to the unit resource grade, effect-grade
-- variables to the unit effect grade

groundˢ : ∀ {Θ} → Subst Θ ∅ˢ
groundˢ = sub (λ _ → Unit) (λ _ → ûᵣ) (λ _ → ûₑ)

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

-- Updating one grade variable: the identity elsewhere

updᵉ : ∀ {Θ} → EVar Θ → EExp Θ → Subst Θ Θ
updᵉ i ε = sub tvar rvar (λ k → if ⌊ k ≟ᶠ i ⌋ then ε else evar k)

updʳ : ∀ {Θ} → RVar Θ → RExp Θ → Subst Θ Θ
updʳ i ρ = sub tvar (λ k → if ⌊ k ≟ᶠ i ⌋ then ρ else rvar k) evar

private
  true≢false : true ≡ false → ⊥
  true≢false ()

  ≟-refl : ∀ {n} → (i : Fin n) → ⌊ i ≟ᶠ i ⌋ ≡ true
  ≟-refl i with i ≟ᶠ i
  ... | yes _ = refl
  ... | no ¬p = ⊥-elim (¬p refl)

-- The updated variable goes to the new image, every other one to itself

updᵉ-hit : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → sE (updᵉ k b) k ≡ b
updᵉ-hit k b with k ≟ᶠ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

updᵉ-miss : ∀ {Ψ} → (k : EVar Ψ) → (b : EExp Ψ) → (i : EVar Ψ)
          → ⌊ k ≟ᶠ i ⌋ ≡ false → sE (updᵉ k b) i ≡ evar i
updᵉ-miss k b i q with i ≟ᶠ k
... | no _     = refl
... | yes refl = ⊥-elim (true≢false (trans (sym (≟-refl k)) q))

updʳ-hit : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → sR (updʳ k b) k ≡ b
updʳ-hit k b with k ≟ᶠ k
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

updʳ-miss : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (i : RVar Ψ)
          → ⌊ k ≟ᶠ i ⌋ ≡ false → sR (updʳ k b) i ≡ rvar i
updʳ-miss k b i q with i ≟ᶠ k
... | no _     = refl
... | yes refl = ⊥-elim (true≢false (trans (sym (≟-refl k)) q))

-- A resource update leaves every effect expression alone

updʳ-e : ∀ {Ψ} → (k : RVar Ψ) → (b : RExp Ψ) → (ε : EExp Ψ) → ε [ updʳ k b ]ᵉ ≡ ε
updʳ-e k b (evar i)   = refl
updʳ-e k b (econst c) = refl
updʳ-e k b (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (updʳ-e k b ε) (updʳ-e k b ε')
updʳ-e k b (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (updʳ-e k b ε) (updʳ-e k b ε')

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
[id]ᵉ (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ ([id]ᵉ ε) ([id]ᵉ ε')

[id]ʳ : ∀ {Θ} → (ρ : RExp Θ) → ρ [ idˢ ]ʳ ≡ ρ
[id]ʳ (rvar i)   = refl
[id]ʳ (rconst ρ) = refl
[id]ʳ (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ ([id]ʳ ρ) ([id]ʳ ρ')
[id]ʳ (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ ([id]ʳ ρ) ([id]ʳ ρ')
[id]ʳ ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ ([id]ᵉ ε)

mutual

  [id]ᵛ : ∀ {Θ} → (A : OVType Θ) → A [ idˢ ]ᵛ ≡ A
  [id]ᵛ (tvar α)  = refl
  [id]ᵛ (Base b)  = refl
  [id]ᵛ Unit      = refl
  [id]ᵛ Bool      = refl
  [id]ᵛ Nat       = refl
  [id]ᵛ (A |×| B) = cong₂ _|×|_ ([id]ᵛ A) ([id]ᵛ B)
  [id]ᵛ (A |+| B) = cong₂ _|+|_ ([id]ᵛ A) ([id]ᵛ B)
  [id]ᵛ (|List| A) = cong |List| ([id]ᵛ A)
  [id]ᵛ Empty     = refl
  [id]ᵛ (A ⇒ C)   = cong₂ _⇒_ ([id]ᵛ A) ([id]ᶜ C)
  [id]ᵛ (C ⇛ D)   = cong₂ _⇛_ ([id]ᶜ C) ([id]ᶜ D)
  [id]ᵛ ([ ρ ] A) = cong₂ [_]_ ([id]ʳ ρ) ([id]ᵛ A)

  [id]ᶜ : ∀ {Θ} → (C : OCType Θ) → C [ idˢ ]ᶜ ≡ C
  [id]ᶜ (A ‼ ε) = cong₂ _‼_ ([id]ᵛ A) ([id]ᵉ ε)

[⨟]ᵉ : ∀ {Θ Θ' Θ''} → (ε : EExp Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
     → ε [ σ ]ᵉ [ δ ]ᵉ ≡ ε [ σ ⨟ˢ δ ]ᵉ
[⨟]ᵉ (evar i)   σ δ = refl
[⨟]ᵉ (econst ε) σ δ = refl
[⨟]ᵉ (ε ·̂ₑ ε')  σ δ = cong₂ _·̂ₑ_ ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)
[⨟]ᵉ (ε ⊔̂ₑ ε')  σ δ = cong₂ _⊔̂ₑ_ ([⨟]ᵉ ε σ δ) ([⨟]ᵉ ε' σ δ)

[⨟]ʳ : ∀ {Θ Θ' Θ''} → (ρ : RExp Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
     → ρ [ σ ]ʳ [ δ ]ʳ ≡ ρ [ σ ⨟ˢ δ ]ʳ
[⨟]ʳ (rvar i)   σ δ = refl
[⨟]ʳ (rconst ρ) σ δ = refl
[⨟]ʳ (ρ ·̂ᵣ ρ')  σ δ = cong₂ _·̂ᵣ_ ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
[⨟]ʳ (ρ ⊔̂ᵣ ρ')  σ δ = cong₂ _⊔̂ᵣ_ ([⨟]ʳ ρ σ δ) ([⨟]ʳ ρ' σ δ)
[⨟]ʳ ∣ ε ∣̂ᵉ     σ δ = cong ∣_∣̂ᵉ ([⨟]ᵉ ε σ δ)

mutual

  [⨟]ᵛ : ∀ {Θ Θ' Θ''} → (A : OVType Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → A [ σ ]ᵛ [ δ ]ᵛ ≡ A [ σ ⨟ˢ δ ]ᵛ
  [⨟]ᵛ (tvar α)  σ δ = refl
  [⨟]ᵛ (Base b)  σ δ = refl
  [⨟]ᵛ Unit      σ δ = refl
  [⨟]ᵛ Bool      σ δ = refl
  [⨟]ᵛ Nat       σ δ = refl
  [⨟]ᵛ (A |×| B) σ δ = cong₂ _|×|_ ([⨟]ᵛ A σ δ) ([⨟]ᵛ B σ δ)
  [⨟]ᵛ (A |+| B) σ δ = cong₂ _|+|_ ([⨟]ᵛ A σ δ) ([⨟]ᵛ B σ δ)
  [⨟]ᵛ (|List| A) σ δ = cong |List| ([⨟]ᵛ A σ δ)
  [⨟]ᵛ Empty     σ δ = refl
  [⨟]ᵛ (A ⇒ C)   σ δ = cong₂ _⇒_ ([⨟]ᵛ A σ δ) ([⨟]ᶜ C σ δ)
  [⨟]ᵛ (C ⇛ D)   σ δ = cong₂ _⇛_ ([⨟]ᶜ C σ δ) ([⨟]ᶜ D σ δ)
  [⨟]ᵛ ([ ρ ] A) σ δ = cong₂ [_]_ ([⨟]ʳ ρ σ δ) ([⨟]ᵛ A σ δ)

  [⨟]ᶜ : ∀ {Θ Θ' Θ''} → (C : OCType Θ) → (σ : Subst Θ Θ') → (δ : Subst Θ' Θ'')
       → C [ σ ]ᶜ [ δ ]ᶜ ≡ C [ σ ⨟ˢ δ ]ᶜ
  [⨟]ᶜ (A ‼ ε) σ δ = cong₂ _‼_ ([⨟]ᵛ A σ δ) ([⨟]ᵉ ε σ δ)

[≐]ᵉ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (ε : EExp Θ) → ε [ σ ]ᵉ ≡ ε [ δ ]ᵉ
[≐]ᵉ p (evar i)   = ≐ᵉ p i
[≐]ᵉ p (econst ε) = refl
[≐]ᵉ p (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ ([≐]ᵉ p ε) ([≐]ᵉ p ε')
[≐]ᵉ p (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ ([≐]ᵉ p ε) ([≐]ᵉ p ε')

[≐]ʳ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (ρ : RExp Θ) → ρ [ σ ]ʳ ≡ ρ [ δ ]ʳ
[≐]ʳ p (rvar i)   = ≐ʳ p i
[≐]ʳ p (rconst ρ) = refl
[≐]ʳ p (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ ([≐]ʳ p ρ) ([≐]ʳ p ρ')
[≐]ʳ p (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ ([≐]ʳ p ρ) ([≐]ʳ p ρ')
[≐]ʳ p ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ ([≐]ᵉ p ε)

mutual

  [≐]ᵛ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (A : OVType Θ) → A [ σ ]ᵛ ≡ A [ δ ]ᵛ
  [≐]ᵛ p (tvar α)  = ≐ᵗ p α
  [≐]ᵛ p (Base b)  = refl
  [≐]ᵛ p Unit      = refl
  [≐]ᵛ p Bool      = refl
  [≐]ᵛ p Nat       = refl
  [≐]ᵛ p (A |×| B) = cong₂ _|×|_ ([≐]ᵛ p A) ([≐]ᵛ p B)
  [≐]ᵛ p (A |+| B) = cong₂ _|+|_ ([≐]ᵛ p A) ([≐]ᵛ p B)
  [≐]ᵛ p (|List| A) = cong |List| ([≐]ᵛ p A)
  [≐]ᵛ p Empty     = refl
  [≐]ᵛ p (A ⇒ C)   = cong₂ _⇒_ ([≐]ᵛ p A) ([≐]ᶜ p C)
  [≐]ᵛ p (C ⇛ D)   = cong₂ _⇛_ ([≐]ᶜ p C) ([≐]ᶜ p D)
  [≐]ᵛ p ([ ρ ] A) = cong₂ [_]_ ([≐]ʳ p ρ) ([≐]ᵛ p A)

  [≐]ᶜ : ∀ {Θ Θ'} {σ δ : Subst Θ Θ'} → σ ≐ˢ δ → (C : OCType Θ) → C [ σ ]ᶜ ≡ C [ δ ]ᶜ
  [≐]ᶜ p (A ‼ ε) = cong₂ _‼_ ([≐]ᵛ p A) ([≐]ᵉ p ε)

wkˢᵗ-e : ∀ {Θ} → (ε : EExp Θ) → ε [ wkˢᵗ ]ᵉ ≡ wkᵗ-e ε
wkˢᵗ-e (evar i)   = refl
wkˢᵗ-e (econst ε) = refl
wkˢᵗ-e (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (wkˢᵗ-e ε) (wkˢᵗ-e ε')
wkˢᵗ-e (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (wkˢᵗ-e ε) (wkˢᵗ-e ε')

wkˢʳ-e : ∀ {Θ} → (ε : EExp Θ) → ε [ wkˢʳ ]ᵉ ≡ wkʳ-e ε
wkˢʳ-e (evar i)   = refl
wkˢʳ-e (econst ε) = refl
wkˢʳ-e (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (wkˢʳ-e ε) (wkˢʳ-e ε')
wkˢʳ-e (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (wkˢʳ-e ε) (wkˢʳ-e ε')

wkˢᵉ-e : ∀ {Θ} → (ε : EExp Θ) → ε [ wkˢᵉ ]ᵉ ≡ wkᵉ-e ε
wkˢᵉ-e (evar i)   = refl
wkˢᵉ-e (econst ε) = refl
wkˢᵉ-e (ε ·̂ₑ ε')  = cong₂ _·̂ₑ_ (wkˢᵉ-e ε) (wkˢᵉ-e ε')
wkˢᵉ-e (ε ⊔̂ₑ ε')  = cong₂ _⊔̂ₑ_ (wkˢᵉ-e ε) (wkˢᵉ-e ε')

wkˢᵗ-r : ∀ {Θ} → (ρ : RExp Θ) → ρ [ wkˢᵗ ]ʳ ≡ wkᵗ-r ρ
wkˢᵗ-r (rvar i)   = refl
wkˢᵗ-r (rconst ρ) = refl
wkˢᵗ-r (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (wkˢᵗ-r ρ) (wkˢᵗ-r ρ')
wkˢᵗ-r (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ (wkˢᵗ-r ρ) (wkˢᵗ-r ρ')
wkˢᵗ-r ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (wkˢᵗ-e ε)

wkˢʳ-r : ∀ {Θ} → (ρ : RExp Θ) → ρ [ wkˢʳ ]ʳ ≡ wkʳ-r ρ
wkˢʳ-r (rvar i)   = refl
wkˢʳ-r (rconst ρ) = refl
wkˢʳ-r (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (wkˢʳ-r ρ) (wkˢʳ-r ρ')
wkˢʳ-r (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ (wkˢʳ-r ρ) (wkˢʳ-r ρ')
wkˢʳ-r ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (wkˢʳ-e ε)

wkˢᵉ-r : ∀ {Θ} → (ρ : RExp Θ) → ρ [ wkˢᵉ ]ʳ ≡ wkᵉ-r ρ
wkˢᵉ-r (rvar i)   = refl
wkˢᵉ-r (rconst ρ) = refl
wkˢᵉ-r (ρ ·̂ᵣ ρ')  = cong₂ _·̂ᵣ_ (wkˢᵉ-r ρ) (wkˢᵉ-r ρ')
wkˢᵉ-r (ρ ⊔̂ᵣ ρ')  = cong₂ _⊔̂ᵣ_ (wkˢᵉ-r ρ) (wkˢᵉ-r ρ')
wkˢᵉ-r ∣ ε ∣̂ᵉ     = cong ∣_∣̂ᵉ (wkˢᵉ-e ε)

mutual

  wkˢᵗ-v : ∀ {Θ} → (A : OVType Θ) → A [ wkˢᵗ ]ᵛ ≡ wkᵗ-v A
  wkˢᵗ-v (tvar α)  = refl
  wkˢᵗ-v (Base b)  = refl
  wkˢᵗ-v Unit      = refl
  wkˢᵗ-v Bool      = refl
  wkˢᵗ-v Nat       = refl
  wkˢᵗ-v (A |×| B) = cong₂ _|×|_ (wkˢᵗ-v A) (wkˢᵗ-v B)
  wkˢᵗ-v (A |+| B) = cong₂ _|+|_ (wkˢᵗ-v A) (wkˢᵗ-v B)
  wkˢᵗ-v (|List| A) = cong |List| (wkˢᵗ-v A)
  wkˢᵗ-v Empty     = refl
  wkˢᵗ-v (A ⇒ C)   = cong₂ _⇒_ (wkˢᵗ-v A) (wkˢᵗ-c C)
  wkˢᵗ-v (C ⇛ D)   = cong₂ _⇛_ (wkˢᵗ-c C) (wkˢᵗ-c D)
  wkˢᵗ-v ([ ρ ] A) = cong₂ [_]_ (wkˢᵗ-r ρ) (wkˢᵗ-v A)

  wkˢᵗ-c : ∀ {Θ} → (C : OCType Θ) → C [ wkˢᵗ ]ᶜ ≡ wkᵗ-c C
  wkˢᵗ-c (A ‼ ε) = cong₂ _‼_ (wkˢᵗ-v A) (wkˢᵗ-e ε)

mutual

  wkˢʳ-v : ∀ {Θ} → (A : OVType Θ) → A [ wkˢʳ ]ᵛ ≡ wkʳ-v A
  wkˢʳ-v (tvar α)  = refl
  wkˢʳ-v (Base b)  = refl
  wkˢʳ-v Unit      = refl
  wkˢʳ-v Bool      = refl
  wkˢʳ-v Nat       = refl
  wkˢʳ-v (A |×| B) = cong₂ _|×|_ (wkˢʳ-v A) (wkˢʳ-v B)
  wkˢʳ-v (A |+| B) = cong₂ _|+|_ (wkˢʳ-v A) (wkˢʳ-v B)
  wkˢʳ-v (|List| A) = cong |List| (wkˢʳ-v A)
  wkˢʳ-v Empty     = refl
  wkˢʳ-v (A ⇒ C)   = cong₂ _⇒_ (wkˢʳ-v A) (wkˢʳ-c C)
  wkˢʳ-v (C ⇛ D)   = cong₂ _⇛_ (wkˢʳ-c C) (wkˢʳ-c D)
  wkˢʳ-v ([ ρ ] A) = cong₂ [_]_ (wkˢʳ-r ρ) (wkˢʳ-v A)

  wkˢʳ-c : ∀ {Θ} → (C : OCType Θ) → C [ wkˢʳ ]ᶜ ≡ wkʳ-c C
  wkˢʳ-c (A ‼ ε) = cong₂ _‼_ (wkˢʳ-v A) (wkˢʳ-e ε)

mutual

  wkˢᵉ-v : ∀ {Θ} → (A : OVType Θ) → A [ wkˢᵉ ]ᵛ ≡ wkᵉ-v A
  wkˢᵉ-v (tvar α)  = refl
  wkˢᵉ-v (Base b)  = refl
  wkˢᵉ-v Unit      = refl
  wkˢᵉ-v Bool      = refl
  wkˢᵉ-v Nat       = refl
  wkˢᵉ-v (A |×| B) = cong₂ _|×|_ (wkˢᵉ-v A) (wkˢᵉ-v B)
  wkˢᵉ-v (A |+| B) = cong₂ _|+|_ (wkˢᵉ-v A) (wkˢᵉ-v B)
  wkˢᵉ-v (|List| A) = cong |List| (wkˢᵉ-v A)
  wkˢᵉ-v Empty     = refl
  wkˢᵉ-v (A ⇒ C)   = cong₂ _⇒_ (wkˢᵉ-v A) (wkˢᵉ-c C)
  wkˢᵉ-v (C ⇛ D)   = cong₂ _⇛_ (wkˢᵉ-c C) (wkˢᵉ-c D)
  wkˢᵉ-v ([ ρ ] A) = cong₂ [_]_ (wkˢᵉ-r ρ) (wkˢᵉ-v A)

  wkˢᵉ-c : ∀ {Θ} → (C : OCType Θ) → C [ wkˢᵉ ]ᶜ ≡ wkᵉ-c C
  wkˢᵉ-c (A ‼ ε) = cong₂ _‼_ (wkˢᵉ-v A) (wkˢᵉ-e ε)

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

⌜⌝ᵍ-subst : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (A : GType) → ⌜ A ⌝ᵍ [ σ ]ᵛ ≡ ⌜ A ⌝ᵍ
⌜⌝ᵍ-subst σ (Base b)   = refl
⌜⌝ᵍ-subst σ Unit       = refl
⌜⌝ᵍ-subst σ Bool       = refl
⌜⌝ᵍ-subst σ Nat        = refl
⌜⌝ᵍ-subst σ Empty      = refl
⌜⌝ᵍ-subst σ (A |×|ᵍ B) = cong₂ _|×|_ (⌜⌝ᵍ-subst σ A) (⌜⌝ᵍ-subst σ B)
⌜⌝ᵍ-subst σ (A |+|ᵍ B) = cong₂ _|+|_ (⌜⌝ᵍ-subst σ A) (⌜⌝ᵍ-subst σ B)
⌜⌝ᵍ-subst σ (|List|ᵍ A) = cong |List| (⌜⌝ᵍ-subst σ A)
⌜⌝ᵍ-subst σ ([ ρ ]ᵍ A) = cong₂ [_]_ refl (⌜⌝ᵍ-subst σ A)

-- Pointwise equality of substitutions is an equivalence, respected by
-- composition, extension and lifting; composition is associative and unital.

≐ˢ-refl : ∀ {Θ Θ'} {σ : Subst Θ Θ'} → σ ≐ˢ σ
≐ˢ-refl = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

≐ˢ-sym : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → σ' ≐ˢ σ
≐ˢ-sym p = mk≐ˢ (λ α → sym (≐ᵗ p α)) (λ i → sym (≐ʳ p i)) (λ i → sym (≐ᵉ p i))

≐ˢ-trans : ∀ {Θ Θ'} {σ σ' σ'' : Subst Θ Θ'} → σ ≐ˢ σ' → σ' ≐ˢ σ'' → σ ≐ˢ σ''
≐ˢ-trans p q = mk≐ˢ (λ α → trans (≐ᵗ p α) (≐ᵗ q α))
                    (λ i → trans (≐ʳ p i) (≐ʳ q i))
                    (λ i → trans (≐ᵉ p i) (≐ᵉ q i))

≐ˢ-,ᵗ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (B : OVType Θ')
      → (σ ,ᵗ B) ≐ˢ (σ' ,ᵗ B)
≐ˢ-,ᵗ p B = mk≐ˢ (λ { zero → refl ; (suc α) → ≐ᵗ p α }) (≐ʳ p) (≐ᵉ p)

≐ˢ-,ʳ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (ρ : RExp Θ')
      → (σ ,ʳ ρ) ≐ˢ (σ' ,ʳ ρ)
≐ˢ-,ʳ p ρ = mk≐ˢ (≐ᵗ p) (λ { zero → refl ; (suc i) → ≐ʳ p i }) (≐ᵉ p)

≐ˢ-,ᵉ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (ε : EExp Θ')
      → (σ ,ᵉ ε) ≐ˢ (σ' ,ᵉ ε)
≐ˢ-,ᵉ p ε = mk≐ˢ (≐ᵗ p) (≐ʳ p) (λ { zero → refl ; (suc i) → ≐ᵉ p i })

≐ˢ-↑ᵉ : ∀ {Θ Θ'} {σ σ' : Subst Θ Θ'} → σ ≐ˢ σ' → (σ ↑ᵉ) ≐ˢ (σ' ↑ᵉ)
≐ˢ-↑ᵉ p = mk≐ˢ (λ α → cong wkᵉ-v (≐ᵗ p α))
               (λ i → cong wkᵉ-r (≐ʳ p i))
               (λ { zero → refl ; (suc i) → cong wkᵉ-e (≐ᵉ p i) })

⨟-idˡ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (idˢ ⨟ˢ σ) ≐ˢ σ
⨟-idˡ σ = ≐ˢ-refl

⨟-idʳ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → (σ ⨟ˢ idˢ) ≐ˢ σ
⨟-idʳ σ = mk≐ˢ (λ α → [id]ᵛ (sTy σ α)) (λ i → [id]ʳ (sR σ i)) (λ i → [id]ᵉ (sE σ i))

⨟-assoc : ∀ {Θ Θ₁ Θ₂ Θ₃} → (σ : Subst Θ Θ₁) → (τ : Subst Θ₁ Θ₂) → (δ : Subst Θ₂ Θ₃)
        → ((σ ⨟ˢ τ) ⨟ˢ δ) ≐ˢ (σ ⨟ˢ (τ ⨟ˢ δ))
⨟-assoc σ τ δ = mk≐ˢ (λ α → [⨟]ᵛ (sTy σ α) τ δ)
                     (λ i → [⨟]ʳ (sR σ i) τ δ)
                     (λ i → [⨟]ᵉ (sE σ i) τ δ)

⨟-congˡ : ∀ {Θ Θ₁ Θ₂} {σ σ' : Subst Θ Θ₁} → σ ≐ˢ σ' → (δ : Subst Θ₁ Θ₂)
        → (σ ⨟ˢ δ) ≐ˢ (σ' ⨟ˢ δ)
⨟-congˡ p δ = mk≐ˢ (λ α → cong (_[ δ ]ᵛ) (≐ᵗ p α))
                   (λ i → cong (_[ δ ]ʳ) (≐ʳ p i))
                   (λ i → cong (_[ δ ]ᵉ) (≐ᵉ p i))

⨟-congʳ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → {δ δ' : Subst Θ₁ Θ₂} → δ ≐ˢ δ'
        → (σ ⨟ˢ δ) ≐ˢ (σ ⨟ˢ δ')
⨟-congʳ σ p = mk≐ˢ (λ α → [≐]ᵛ p (sTy σ α))
                   (λ i → [≐]ʳ p (sR σ i))
                   (λ i → [≐]ᵉ p (sE σ i))

-- Lifting preserves the identity and composition

↑ᵉ-id : ∀ {Θ} → (idˢ {Θ} ↑ᵉ) ≐ˢ idˢ
↑ᵉ-id = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

⨟-↑ᵉ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (δ : Subst Θ₁ Θ₂)
     → ((σ ↑ᵉ) ⨟ˢ (δ ↑ᵉ)) ≐ˢ ((σ ⨟ˢ δ) ↑ᵉ)
⨟-↑ᵉ σ δ = mk≐ˢ (λ α → wk-↑ᵉ-v δ (sTy σ α))
                (λ i → wk-↑ᵉ-r δ (sR σ i))
                (λ { zero → refl ; (suc i) → wk-↑ᵉ-e δ (sE σ i) })

-- A weakening followed by an extension cancels, after any substitution

wk-,ᵗ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (B : OVType Θ')
        → ((ι ⨟ˢ wkˢᵗ) ⨟ˢ (σ ,ᵗ B)) ≐ˢ (ι ⨟ˢ σ)
wk-,ᵗ-ˢ ι σ B = ≐ˢ-trans (⨟-assoc ι wkˢᵗ (σ ,ᵗ B)) (⨟-congʳ ι (wkˢᵗ-,ᵗ σ B))

wk-,ʳ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (ρ : RExp Θ')
        → ((ι ⨟ˢ wkˢʳ) ⨟ˢ (σ ,ʳ ρ)) ≐ˢ (ι ⨟ˢ σ)
wk-,ʳ-ˢ ι σ ρ = ≐ˢ-trans (⨟-assoc ι wkˢʳ (σ ,ʳ ρ)) (⨟-congʳ ι (wkˢʳ-,ʳ σ ρ))

wk-,ᵉ-ˢ : ∀ {Θ₀ Θ Θ'} → (ι : Subst Θ₀ Θ) → (σ : Subst Θ Θ') → (ε : EExp Θ')
        → ((ι ⨟ˢ wkˢᵉ) ⨟ˢ (σ ,ᵉ ε)) ≐ˢ (ι ⨟ˢ σ)
wk-,ᵉ-ˢ ι σ ε = ≐ˢ-trans (⨟-assoc ι wkˢᵉ (σ ,ᵉ ε)) (⨟-congʳ ι (wkˢᵉ-,ᵉ σ ε))

-- A substitution with its images tabulated

memo : ∀ {Θ Θ'} → Subst Θ Θ' → Subst Θ Θ'
memo {Θ} {Θ'} σ = fromTables (tabulate (sTy σ)) (tabulate (sR σ)) (tabulate (sE σ))
  where
    fromTables : Vec (OVType Θ') (nTy Θ) → Vec (RExp Θ') (nR Θ) → Vec (EExp Θ') (nE Θ)
               → Subst Θ Θ'
    fromTables ts rs es = sub (lookupᵛ ts) (lookupᵛ rs) (lookupᵛ es)

memo-≐ : ∀ {Θ Θ'} → (σ : Subst Θ Θ') → memo σ ≐ˢ σ
memo-≐ σ = mk≐ˢ (lookup∘tabulate (sTy σ)) (lookup∘tabulate (sR σ)) (lookup∘tabulate (sE σ))

------------------------------------------------------------------------
-- Juxtaposition of scopes

-- `Θ ⊹ Ψ` extends `Θ` by the variables of `Ψ`, the new ones innermost;
-- `wkˢ⊹` and `newˢ⊹` inject the two scopes.

infixl 30 _⊹_

_⊹_ : Scope → Scope → Scope
Θ ⊹ Ψ = scope (nTy Ψ + nTy Θ) (nR Ψ + nR Θ) (nE Ψ + nE Θ)

wkˢ⊹ : ∀ {Θ} → (Ψ : Scope) → Subst Θ (Θ ⊹ Ψ)
wkˢ⊹ Ψ = sub (λ α → tvar (nTy Ψ ↑ʳ α)) (λ i → rvar (nR Ψ ↑ʳ i)) (λ i → evar (nE Ψ ↑ʳ i))

newˢ⊹ : ∀ {Θ} → (Ψ : Scope) → Subst Ψ (Θ ⊹ Ψ)
newˢ⊹ {Θ} Ψ = sub (λ α → tvar (α ↑ˡ nTy Θ)) (λ i → rvar (i ↑ˡ nR Θ)) (λ i → evar (i ↑ˡ nE Θ))

-- Extending a substitution by images for the variables of one sort,
-- the innermost first

_⊕ᵗ_ : ∀ {Θ Θ' a} → Subst Θ Θ' → (Fin a → OVType Θ')
     → Subst (scope (a + nTy Θ) (nR Θ) (nE Θ)) Θ'
_⊕ᵗ_ {a = zero}  σ ts = σ
_⊕ᵗ_ {a = suc a} σ ts = (σ ⊕ᵗ (λ α → ts (suc α))) ,ᵗ ts zero

_⊕ʳ_ : ∀ {Θ Θ' b} → Subst Θ Θ' → (Fin b → RExp Θ')
     → Subst (scope (nTy Θ) (b + nR Θ) (nE Θ)) Θ'
_⊕ʳ_ {b = zero}  σ rs = σ
_⊕ʳ_ {b = suc b} σ rs = (σ ⊕ʳ (λ i → rs (suc i))) ,ʳ rs zero

_⊕ᵉ_ : ∀ {Θ Θ' c} → Subst Θ Θ' → (Fin c → EExp Θ')
     → Subst (scope (nTy Θ) (nR Θ) (c + nE Θ)) Θ'
_⊕ᵉ_ {c = zero}  σ es = σ
_⊕ᵉ_ {c = suc c} σ es = (σ ⊕ᵉ (λ i → es (suc i))) ,ᵉ es zero

-- The pair of substitutions of the two scopes

infixl 28 _⊕ˢ_

_⊕ˢ_ : ∀ {Θ Ψ Θ'} → Subst Θ Θ' → Subst Ψ Θ' → Subst (Θ ⊹ Ψ) Θ'
σ ⊕ˢ δ = ((σ ⊕ᵗ sTy δ) ⊕ʳ sR δ) ⊕ᵉ sE δ

private

  -- each extension acts on its own sort and leaves the others alone

  ⊕ᵗ-old : ∀ {Θ Θ' a} (σ : Subst Θ Θ') (ts : Fin a → OVType Θ') (α : TyVar Θ)
         → sTy (σ ⊕ᵗ ts) (a ↑ʳ α) ≡ sTy σ α
  ⊕ᵗ-old {a = zero}  σ ts α = refl
  ⊕ᵗ-old {a = suc a} σ ts α = ⊕ᵗ-old σ (λ β → ts (suc β)) α

  ⊕ᵗ-new : ∀ {Θ Θ' a} (σ : Subst Θ Θ') (ts : Fin a → OVType Θ') (α : Fin a)
         → sTy (σ ⊕ᵗ ts) (α ↑ˡ nTy Θ) ≡ ts α
  ⊕ᵗ-new {a = suc a} σ ts zero    = refl
  ⊕ᵗ-new {a = suc a} σ ts (suc α) = ⊕ᵗ-new σ (λ β → ts (suc β)) α

  ⊕ᵗ-R : ∀ {Θ Θ' a} (σ : Subst Θ Θ') (ts : Fin a → OVType Θ') (i : RVar Θ)
       → sR (σ ⊕ᵗ ts) i ≡ sR σ i
  ⊕ᵗ-R {a = zero}  σ ts i = refl
  ⊕ᵗ-R {a = suc a} σ ts i = ⊕ᵗ-R σ (λ β → ts (suc β)) i

  ⊕ᵗ-E : ∀ {Θ Θ' a} (σ : Subst Θ Θ') (ts : Fin a → OVType Θ') (i : EVar Θ)
       → sE (σ ⊕ᵗ ts) i ≡ sE σ i
  ⊕ᵗ-E {a = zero}  σ ts i = refl
  ⊕ᵗ-E {a = suc a} σ ts i = ⊕ᵗ-E σ (λ β → ts (suc β)) i

  ⊕ʳ-old : ∀ {Θ Θ' b} (σ : Subst Θ Θ') (rs : Fin b → RExp Θ') (i : RVar Θ)
         → sR (σ ⊕ʳ rs) (b ↑ʳ i) ≡ sR σ i
  ⊕ʳ-old {b = zero}  σ rs i = refl
  ⊕ʳ-old {b = suc b} σ rs i = ⊕ʳ-old σ (λ j → rs (suc j)) i

  ⊕ʳ-new : ∀ {Θ Θ' b} (σ : Subst Θ Θ') (rs : Fin b → RExp Θ') (i : Fin b)
         → sR (σ ⊕ʳ rs) (i ↑ˡ nR Θ) ≡ rs i
  ⊕ʳ-new {b = suc b} σ rs zero    = refl
  ⊕ʳ-new {b = suc b} σ rs (suc i) = ⊕ʳ-new σ (λ j → rs (suc j)) i

  ⊕ʳ-T : ∀ {Θ Θ' b} (σ : Subst Θ Θ') (rs : Fin b → RExp Θ') (α : TyVar Θ)
       → sTy (σ ⊕ʳ rs) α ≡ sTy σ α
  ⊕ʳ-T {b = zero}  σ rs α = refl
  ⊕ʳ-T {b = suc b} σ rs α = ⊕ʳ-T σ (λ j → rs (suc j)) α

  ⊕ʳ-E : ∀ {Θ Θ' b} (σ : Subst Θ Θ') (rs : Fin b → RExp Θ') (i : EVar Θ)
       → sE (σ ⊕ʳ rs) i ≡ sE σ i
  ⊕ʳ-E {b = zero}  σ rs i = refl
  ⊕ʳ-E {b = suc b} σ rs i = ⊕ʳ-E σ (λ j → rs (suc j)) i

  ⊕ᵉ-old : ∀ {Θ Θ' c} (σ : Subst Θ Θ') (es : Fin c → EExp Θ') (i : EVar Θ)
         → sE (σ ⊕ᵉ es) (c ↑ʳ i) ≡ sE σ i
  ⊕ᵉ-old {c = zero}  σ es i = refl
  ⊕ᵉ-old {c = suc c} σ es i = ⊕ᵉ-old σ (λ j → es (suc j)) i

  ⊕ᵉ-new : ∀ {Θ Θ' c} (σ : Subst Θ Θ') (es : Fin c → EExp Θ') (i : Fin c)
         → sE (σ ⊕ᵉ es) (i ↑ˡ nE Θ) ≡ es i
  ⊕ᵉ-new {c = suc c} σ es zero    = refl
  ⊕ᵉ-new {c = suc c} σ es (suc i) = ⊕ᵉ-new σ (λ j → es (suc j)) i

  ⊕ᵉ-T : ∀ {Θ Θ' c} (σ : Subst Θ Θ') (es : Fin c → EExp Θ') (α : TyVar Θ)
       → sTy (σ ⊕ᵉ es) α ≡ sTy σ α
  ⊕ᵉ-T {c = zero}  σ es α = refl
  ⊕ᵉ-T {c = suc c} σ es α = ⊕ᵉ-T σ (λ j → es (suc j)) α

  ⊕ᵉ-R : ∀ {Θ Θ' c} (σ : Subst Θ Θ') (es : Fin c → EExp Θ') (i : RVar Θ)
       → sR (σ ⊕ᵉ es) i ≡ sR σ i
  ⊕ᵉ-R {c = zero}  σ es i = refl
  ⊕ᵉ-R {c = suc c} σ es i = ⊕ᵉ-R σ (λ j → es (suc j)) i

-- The pair restricts to each of its components

wkˢ⊹-⊕ˢ : ∀ {Θ Ψ Θ'} → (σ : Subst Θ Θ') → (δ : Subst Ψ Θ') → (wkˢ⊹ Ψ ⨟ˢ (σ ⊕ˢ δ)) ≐ˢ σ
wkˢ⊹-⊕ˢ {Ψ = Ψ} σ δ =
  mk≐ˢ (λ α → trans (⊕ᵉ-T _ (sE δ) _) (trans (⊕ʳ-T _ (sR δ) _) (⊕ᵗ-old σ (sTy δ) α)))
       (λ i → trans (⊕ᵉ-R _ (sE δ) _) (trans (⊕ʳ-old _ (sR δ) i) (⊕ᵗ-R σ (sTy δ) i)))
       (λ i → trans (⊕ᵉ-old _ (sE δ) i) (trans (⊕ʳ-E _ (sR δ) i) (⊕ᵗ-E σ (sTy δ) i)))

newˢ⊹-⊕ˢ : ∀ {Θ Ψ Θ'} → (σ : Subst Θ Θ') → (δ : Subst Ψ Θ') → (newˢ⊹ Ψ ⨟ˢ (σ ⊕ˢ δ)) ≐ˢ δ
newˢ⊹-⊕ˢ {Ψ = Ψ} σ δ =
  mk≐ˢ (λ α → trans (⊕ᵉ-T _ (sE δ) _) (trans (⊕ʳ-T _ (sR δ) _) (⊕ᵗ-new σ (sTy δ) α)))
       (λ i → trans (⊕ᵉ-R _ (sE δ) _) (⊕ʳ-new _ (sR δ) i))
       (λ i → ⊕ᵉ-new _ (sE δ) i)

