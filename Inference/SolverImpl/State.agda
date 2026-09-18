------------------------------------------------------------------
-- The solver state                                              --
--                                                                --
-- A state `St Θ` is a scope `Ψ` of variables still unknown, the   --
-- substitution `θ : Subst Θ Ψ` found so far, the residual over    --
-- `Ψ` still to be discharged, and the effect-grade variables of   --
-- `Ψ` that are rigid.                                             --
--                                                                --
-- A morphism `s ⟶ s'` is the driver's one legal move: a further   --
-- substitution `δ` that factors the old solution through the new  --
-- one and along which a discharge of the new residual is a        --
-- discharge of the old. Morphisms compose, and that composition   --
-- is what threads a conjunction.                                  --
------------------------------------------------------------------

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base using (List; []; _∷_; mapMaybe)
open import Data.Maybe.Base using (Maybe; just; nothing)

open import Syntax.Grades
open import Syntax.LanguageSpec

open import Util.Equality

open import Inference.Scopes

module Inference.SolverImpl.State (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades

open import Inference.Open.Grades S
open import Inference.Open.Types  S
open import Inference.Open.Subst  S
open import Inference.Open.Hyps   S

open import Inference.Constraints.Properties S using (≐ˢ-sym)

open import Inference.SolverImpl.Core.Unify S using (Rig)
open import Inference.SolverImpl.Resid      S

--------------------------------------------------------------
-- The algebra of pointwise equality                         --
--------------------------------------------------------------

≐ˢ-refl : ∀ {Θ Θ'} {σ : Subst Θ Θ'} → σ ≐ˢ σ
≐ˢ-refl = mk≐ˢ (λ α → refl) (λ i → refl) (λ i → refl)

≐ˢ-trans : ∀ {Θ Θ'} {σ σ' σ'' : Subst Θ Θ'} → σ ≐ˢ σ' → σ' ≐ˢ σ'' → σ ≐ˢ σ''
≐ˢ-trans p q = mk≐ˢ (λ α → trans (≐ᵗ p α) (≐ᵗ q α))
                    (λ i → trans (≐ʳ p i) (≐ʳ q i))
                    (λ i → trans (≐ᵉ p i) (≐ᵉ q i))

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

-- Two lifts compose to the lift of the composite

⨟-↑ᵉ : ∀ {Θ Θ₁ Θ₂} → (σ : Subst Θ Θ₁) → (δ : Subst Θ₁ Θ₂)
     → ((σ ↑ᵉ) ⨟ˢ (δ ↑ᵉ)) ≐ˢ ((σ ⨟ˢ δ) ↑ᵉ)
⨟-↑ᵉ σ δ = mk≐ˢ (λ α → wk-↑ᵉ-v δ (sTy σ α))
                (λ i → wk-↑ᵉ-r δ (sR σ i))
                (λ { zero → refl ; (suc i) → wk-↑ᵉ-e δ (sE σ i) })

--------------------------------------------------------------
-- Reading an existential witness back off a substitution    --
--                                                           --
-- A substitution out of an extended scope is its own         --
-- restriction extended by the image of the new variable.     --
--------------------------------------------------------------

↑-,ᵗ : ∀ {Θ Θ'} → (γ : Subst (Θ +ty) Θ')
     → ((wkˢᵗ ⨟ˢ γ) ,ᵗ sTy γ (newᵗ {Θ})) ≐ˢ γ
↑-,ᵗ γ = mk≐ˢ (λ { zero → refl ; (suc α) → refl }) (λ i → refl) (λ i → refl)

↑-,ʳ : ∀ {Θ Θ'} → (γ : Subst (Θ +r) Θ')
     → ((wkˢʳ ⨟ˢ γ) ,ʳ sR γ (newʳ {Θ})) ≐ˢ γ
↑-,ʳ γ = mk≐ˢ (λ α → refl) (λ { zero → refl ; (suc i) → refl }) (λ i → refl)

↑-,ᵉ : ∀ {Θ Θ'} → (γ : Subst (Θ +e) Θ')
     → ((wkˢᵉ ⨟ˢ γ) ,ᵉ sE γ (newᵉ {Θ})) ≐ˢ γ
↑-,ᵉ γ = mk≐ˢ (λ α → refl) (λ i → refl) (λ { zero → refl ; (suc i) → refl })

--------------------------------------------------------------
-- Transporting the rigids                                   --
--                                                           --
-- A rigid is never bound, so its image under any substitution --
-- the driver builds is again a variable.                      --
--------------------------------------------------------------

varᵉ? : ∀ {Ψ} → EExp Ψ → Maybe (EVar Ψ)
varᵉ? (evar i)  = just i
varᵉ? (econst c) = nothing
varᵉ? (ε ·̂ₑ ε') = nothing

transRig : ∀ {Ψ Ψ'} → Subst Ψ Ψ' → Rig Ψ → Rig Ψ'
transRig δ rg = mapMaybe (λ i → varᵉ? (sE δ i)) rg

--------------------------------------------------------------
-- States                                                    --
--------------------------------------------------------------

record St (Θ : Scope) : Set where
  constructor st
  field
    Ψ   : Scope                 -- the variables still unknown
    θ   : Subst Θ Ψ             -- the solution so far
    res : Resid Ψ               -- what is left over
    rig : Rig Ψ                 -- the rigid effect-grade variables

open St public

init : ∀ {Θ} → St Θ
init {Θ} = st Θ idˢ emptyᴿ []

--------------------------------------------------------------
-- Morphisms of states                                       --
--------------------------------------------------------------

infix 4 _⟶_

record _⟶_ {Θ : Scope} (s s' : St Θ) : Set where
  constructor mor
  field
    mδ   : Subst (Ψ s) (Ψ s')
    mtri : (θ s ⨟ˢ mδ) ≐ˢ θ s'
    mres : ∀ {Ψ''} → (δ : Subst (Ψ s') Ψ'') → (Q : Hyps Ψ'')
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

--------------------------------------------------------------
-- Binder lifts                                              --
--                                                           --
-- An existential allocates a fresh unknown; the rigid lift    --
-- additionally declares it rigid and starts the scope with a  --
-- fresh residual, so that what is left over inside a rigid    --
-- scope is exactly what has to cross its boundary.            --
--------------------------------------------------------------

infixl 32 _↑ᵗˢ _↑ʳˢ _↑ᵉˢ

_↑ᵗˢ : ∀ {Θ} → St Θ → St (Θ +ty)
s ↑ᵗˢ = st (Ψ s +ty) (θ s ↑ᵗ) (res s [ wkˢᵗ {Ψ s} ]ᴿ) (transRig (wkˢᵗ {Ψ s}) (rig s))

_↑ʳˢ : ∀ {Θ} → St Θ → St (Θ +r)
s ↑ʳˢ = st (Ψ s +r) (θ s ↑ʳ) (res s [ wkˢʳ {Ψ s} ]ᴿ) (transRig (wkˢʳ {Ψ s}) (rig s))

_↑ᵉˢ : ∀ {Θ} → St Θ → St (Θ +e)
s ↑ᵉˢ = st (Ψ s +e) (θ s ↑ᵉ) (res s [ wkˢᵉ {Ψ s} ]ᴿ) (transRig (wkˢᵉ {Ψ s}) (rig s))

⇑ᵉˢ : ∀ {Θ} → St Θ → St (Θ +e)
⇑ᵉˢ s = st (Ψ s +e) (θ s ↑ᵉ) emptyᴿ (newᵉ {Ψ s} ∷ transRig (wkˢᵉ {Ψ s}) (rig s))
