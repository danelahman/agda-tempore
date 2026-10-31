------------------------------------------------------------------
-- The solver state                                             --
--                                                              --
-- A state `St Θ` is a scope `Ω` of the variables still         --
-- unknown, the substitution `θ : Subst Θ Ω` found so far, the  --
-- residual over `Ω`, and the rigid effect-grade variables of   --
-- `Ω`. A morphism `s ⟶ s'` is a move of the driver: a          --
-- substitution `δ` extending `θ` to the new one, along which a --
-- discharge of the new residual is one of the old. Morphisms   --
-- compose.                                                     --
------------------------------------------------------------------

open import Data.Bool.Base using (_∨_; true; false) renaming (Bool to 𝔹)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List.Base using (List; []; _∷_; mapMaybe)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)

open import Relation.Nullary.Decidable using (⌊_⌋)

open import Grades.Base
open import Language.Spec

open import Util.Equality

open import PolymorphicCalculus.Syntax.Scopes

module PolymorphicCalculus.Inference.SolverImpl.State (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import PolymorphicCalculus.Syntax.Grades            S
open import PolymorphicCalculus.Syntax.Types             S
open import PolymorphicCalculus.Syntax.GradeSubstitution S
open import PolymorphicCalculus.Hypotheses               S

open import PolymorphicCalculus.Inference.SolverImpl.Resid S

-- A substitution out of an extended scope is its restriction extended by the
-- image of the new variable

↑-,ᵗ : ∀ {Θ Θ'} → (γ : Subst (Θ +ty) Θ')
     → ((wkˢᵗ ⨟ˢ γ) ,ᵗ sTy γ (newᵗ {Θ})) ≐ˢ γ
↑-,ᵗ γ = mk≐ˢ (λ { zero → refl ; (suc α) → refl }) (λ i → refl) (λ i → refl)

↑-,ʳ : ∀ {Θ Θ'} → (γ : Subst (Θ +r) Θ')
     → ((wkˢʳ ⨟ˢ γ) ,ʳ sR γ (newʳ {Θ})) ≐ˢ γ
↑-,ʳ γ = mk≐ˢ (λ α → refl) (λ { zero → refl ; (suc i) → refl }) (λ i → refl)

↑-,ᵉ : ∀ {Θ Θ'} → (γ : Subst (Θ +e) Θ')
     → ((wkˢᵉ ⨟ˢ γ) ,ᵉ sE γ (newᵉ {Θ})) ≐ˢ γ
↑-,ᵉ γ = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

-- The rigid effect-grade variables

Rig : Scope → Set
Rig Θ = List (EVar Θ)

-- Membership, at the bare `Fin` a variable of a scope is

_∈ᶠ_ : ∀ {n} → Fin n → List (Fin n) → 𝔹
i ∈ᶠ []       = false
i ∈ᶠ (j ∷ js) = ⌊ i ≟ᶠ j ⌋ ∨ (i ∈ᶠ js)

-- A substitution fixes the rigids when it sends them to distinct variables

record Fixing {Θ Ω : Scope} (rg : Rig Θ) (σ : Subst Θ Ω) : Set where
  constructor fixing
  field
    fixᵉ : (i : EVar Θ) → i ∈ᶠ rg ≡ true → Σ[ j ∈ EVar Ω ] (sE σ i ≡ evar j)
    injᵉ : (i i' : EVar Θ) → i ∈ᶠ rg ≡ true → i' ∈ᶠ rg ≡ true → sE σ i ≡ sE σ i' → i ≡ i'

open Fixing public

-- A rigid is never bound, so its image under the driver's substitutions is a
-- variable

varᵉ? : ∀ {Ω} → EExp Ω → Maybe (EVar Ω)
varᵉ? (evar i)  = just i
varᵉ? (econst c) = nothing
varᵉ? (ε ·̂ₑ ε') = nothing
varᵉ? (ε ⊔̂ₑ ε') = nothing

transRig : ∀ {Ω Ω'} → Subst Ω Ω' → Rig Ω → Rig Ω'
transRig δ rg = mapMaybe (λ i → varᵉ? (sE δ i)) rg

record St (Θ : Scope) : Set where
  constructor st
  field
    Ω   : Scope                 -- the variables still unknown
    θ   : Subst Θ Ω             -- the solution so far
    res : Resid Ω               -- what is left over
    rig : Rig Ω                 -- the rigid effect-grade variables

open St public

init : ∀ {Θ} → St Θ
init {Θ} = st Θ idˢ emptyᴿ []

infix 4 _⟶_

record _⟶_ {Θ : Scope} (s s' : St Θ) : Set where
  constructor mor
  field
    mδ   : Subst (Ω s) (Ω s')
    mtri : (θ s ⨟ˢ mδ) ≐ˢ θ s'
    mres : ∀ {Ω''} → (δ : Subst (Ω s') Ω'') → (Q : Hyps Ω'')
         → Q ⊩ᴿ (res s') [ δ ] → Q ⊩ᴿ (res s) [ mδ ⨟ˢ δ ]

open _⟶_ public

⟶-id : ∀ {Θ} → {s : St Θ} → s ⟶ s
⟶-id {s = s} = mor idˢ (⨟-idʳ (θ s)) (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-idˡ δ)) h)

⟶-⨟ : ∀ {Θ} → {s s' s'' : St Θ} → s ⟶ s' → s' ⟶ s'' → s ⟶ s''
⟶-⨟ {s = s} m m' =
  mor (mδ m ⨟ˢ mδ m')
      (≐ˢ-trans (≐ˢ-sym (⨟-assoc (θ s) (mδ m) (mδ m')))
                (≐ˢ-trans (⨟-congˡ (mtri m) (mδ m')) (mtri m')))
      (λ δ Q h → ⊩ᴿ-resp-≐ˢ (≐ˢ-sym (⨟-assoc (mδ m) (mδ m') δ))
                            (mres m (mδ m' ⨟ˢ δ) Q (mres m' δ Q h)))

-- An existential allocates a fresh unknown; the rigid lift also declares it
-- rigid and starts the scope with a fresh residual

infixl 32 _↑ᵗˢ _↑ʳˢ _↑ᵉˢ

_↑ᵗˢ : ∀ {Θ} → St Θ → St (Θ +ty)
s ↑ᵗˢ = st (Ω s +ty) (θ s ↑ᵗ) (res s [ wkˢᵗ {Ω s} ]ᴿ) (transRig (wkˢᵗ {Ω s}) (rig s))

_↑ʳˢ : ∀ {Θ} → St Θ → St (Θ +r)
s ↑ʳˢ = st (Ω s +r) (θ s ↑ʳ) (res s [ wkˢʳ {Ω s} ]ᴿ) (transRig (wkˢʳ {Ω s}) (rig s))

_↑ᵉˢ : ∀ {Θ} → St Θ → St (Θ +e)
s ↑ᵉˢ = st (Ω s +e) (θ s ↑ᵉ) (res s [ wkˢᵉ {Ω s} ]ᴿ) (transRig (wkˢᵉ {Ω s}) (rig s))

⇑ᵉˢ : ∀ {Θ} → St Θ → St (Θ +e)
⇑ᵉˢ s = st (Ω s +e) (θ s ↑ᵉ) emptyᴿ (newᵉ {Ω s} ∷ transRig (wkˢᵉ {Ω s}) (rig s))
