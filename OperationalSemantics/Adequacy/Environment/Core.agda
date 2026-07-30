------------------------------------------------------------------------
-- Closing environments: lock-free contexts, `Env`, and its reducibility predicates.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no; ¬_; Dec)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Environment.Core (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts      Spec
open import Syntax.Language      Spec
open import Syntax.RenActions    Spec
open import Syntax.Renamings     Spec
open import Syntax.Substitutions Spec
open import Syntax.Types         Spec

open import OperationalSemantics.Adequacy.Reducibility   Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import Syntax.Substitutions.Weakening Spec
open import Syntax.Substitutions.Renaming  Spec
open import Syntax.Substitutions.Swap      Spec
open import OperationalSemantics.Adequacy.GradedReach          Spec
open import Syntax.Substitutions.Equivalence Spec

-- Closed values for an eternal prefix.

ClosedVals : Ctx → Set
ClosedVals Δ = ∀ {A ρ} → A ∈[ ρ ] Δ → [] ⊢V⦂ A

-- LOCK-FREE CONTEXTS
--
-- `_ᴱ` drops every lock, so the eternal prefix is lock-free — which is what
-- makes a closed value weakenable into it: `Ren [] Γ` [] exists exactly when `Γ`
-- has no lock, crossing one needing `ρ ≾ᵣ uᵣ`.

data Lock-free : Ctx → Set where
  lf-[] : Lock-free []
  lf-∷  : ∀ {Γ A} → Lock-free Γ → Lock-free (Γ ∷ A)

-- The decision is routed through a helper *taking* it rather than matching
-- on it, as `_ᴱ` itself is (`ᴱ-∷`): a caller that has decided `A`'s
-- eternality can then see the witness reduce, which `with`/`rewrite` at the
-- use site cannot achieve — `eternal? A` does not occur syntactically in
-- `ᴱ-lock-free (Γ ∷ A)`, only inside its own `with`.

ᴱ-lock-free   : (Γ : Ctx) → Lock-free (Γ ᴱ)
ᴱ-lock-free-∷ : (Γ : Ctx) → (A : VType) → (d : Dec (Eternal A))
              → Lock-free (ᴱ-∷ (Γ ᴱ) A d)

ᴱ-lock-free []        = lf-[]
ᴱ-lock-free (Γ ∷ A)   = ᴱ-lock-free-∷ Γ A (eternal? A)
ᴱ-lock-free (Γ ⟨ ρ ⟩) = ᴱ-lock-free Γ

ᴱ-lock-free-∷ Γ A (yes _) = lf-∷ (ᴱ-lock-free Γ)
ᴱ-lock-free-∷ Γ A (no  _) = ᴱ-lock-free Γ

-- Weakening a closed term into a lock-free context, and a term into one
-- left-extended by a lock-free prefix.

empty-ren : ∀ {Δ} → Lock-free Δ → Ren [] Δ []
empty-ren lf-[]     = id-ren
empty-ren (lf-∷ lf) = empty-ren lf ∘ʳ wk-ren

eternal-wk : ∀ {Δ} → Lock-free Δ → (Γ : Ctx) → Ren [] (Δ ++ᶜ Γ) Γ
eternal-wk lf []        = empty-ren lf
eternal-wk lf (Γ ∷ A)   = cong-∷-ren (eternal-wk lf Γ)
eternal-wk lf (Γ ⟨ ρ ⟩) = cong-⟨⟩-ren (eternal-wk lf Γ)

-- Weakening a *closed* term into a state's context. Locks are crossed by
-- `⟨⟩-ext-ctx`, which asks for everything to their left to be eternal — and here
-- that is `[]`, vacuously. Which such renaming is chosen never matters: `_≐ʳ_`
-- compares renamings on variables, and `[]` has none (`∅-ren-≐`).

∅-ren : (St : 𝕊 []) → Ren [] (toCtx St) []
∅-ren St = wk-ctx-ren ec-[] (toCtx St)

∅-ren-≐ : ∀ {Γ} → (r r' : Ren [] Γ []) → r ≐ʳ r'
∅-ren-≐ r r' = mk≐ʳ (λ ())

-- A closing environment: how `Γ` is closed down to the state context.

infixl 30 _∷ᵉ_
infix  32 _⟨_⟩ᵉ

data Env : (St : 𝕊 []) → Ctx → Set where

  ⌊_⌋      : (St : 𝕊 [])
           ------------------
           → Env St (toCtx St)

  -- the empty context at a state, which is where a handler clause closes:
  -- `toCtx St ᴱ` is `[]` (cells are box-typed, never eternal), so a clause has
  -- no free state variable. Routing that through `⌊ St ⌋` instead would demand
  -- the store, for cells the clause cannot mention.

  ∅ᵉ       : (St : 𝕊 [])
           --------------
           → Env St []

  -- postcomposition with a reach: what makes `Env` functorial in the *state*
  -- (`env-alloc`). Recorded rather than pushed into the base, so that a
  -- reducible environment stays reducible when the state grows: its values
  -- still come from the earlier state, and `Val-reach` moves them. Pushing it
  -- into `⌊_⌋` would instead demand the *later* state's store, which nothing
  -- supplies.

  reachᵉ   : ∀ {St St' Γ}
           → Env St Γ → St ⊑ₛ[ uᵣ ] St'
           ------------------------------
           → Env St' Γ

  -- a lock, matched by any state far enough ahead

  _⟨_⟩ᵉ    : ∀ {St St' Γ ρ}
           → Env St Γ → St ⊑ₛ[ ρ ] St'
           ------------------------------
           → Env St' (Γ ⟨ ρ ⟩)

  _∷ᵉ_     : ∀ {St Γ A}
           → Env St Γ → toCtx St ⊢V⦂ A
           ---------------------------
           → Env St (Γ ∷ A)

  -- a binder matched by a freshly allocated cell: `BOX` steps
  -- `⟨St, box V M⟩ ↝ ⟨St ∷ₛ V', M⟩`, and the reduct already lives over the new
  -- state's context, so the environment must *keep* the binder as the cell
  -- rather than substitute a variable for itself. Pure re-bracketing: it acts as
  -- `γ` under the suffix `[] ∷ [ ρ ] A`.

  liftᵉ    : ∀ {St Γ A ρ}
           → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A) → Env St Γ
           ------------------------------------------------
           → Env (St ∷ₛ V) (Γ ∷ [ ρ ] A)

  eternalˡ : ∀ {St Γ}
           → (Δ : Ctx) → Lock-free Δ → ClosedVals Δ → Env St Γ
           ---------------------------------------------------
           → Env St (Δ ++ᶜ Γ)

-- REDUCIBLE ENVIRONMENTS
--
-- The state's own part is the store; each instantiated binder holds a
-- reducible value. Of the eternal prefix nothing is asked beyond its types
-- being eternal, at which `Val` holds of everything (`Val-eternal`) — that is
-- the only thing that makes a *closed* value usable where a lock stands.

Rel-Env : ∀ {St Γ} → Env St Γ → Set
Rel-Env ⌊ St ⌋                = Store St
Rel-Env (∅ᵉ St)                = ⊤
Rel-Env (γ ⟨ q ⟩ᵉ)             = Rel-Env γ
Rel-Env (_∷ᵉ_ {St} {Γ} {A} γ V) = Rel-Env γ × Val A St V
Rel-Env (liftᵉ {St} {Γ} {A} {ρ} V γ) =
  Rel-Env γ
  × (∀ {St'} → (q : St ⊑ₛ[ ρ ] St')
       → Val A St' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V))
Rel-Env (reachᵉ γ q)           = Rel-Env γ
Rel-Env (eternalˡ Δ lf η γ)    =
  Rel-Env γ × (∀ {A ρ} → A ∈[ ρ ] Δ → Eternal A)

-- ETERNAL PREFIXES CARRY ETERNAL TYPES
--
-- The part of `Rel-Env` the purely syntactic laws below need: an eternal
-- prefix's variables are of eternal type, so a variable of a non-eternal type
-- never comes from one. Kept apart from `Rel-Env` so that those laws do not
-- mention the store or the logical relation.

Eternal-Env : ∀ {St Γ} → Env St Γ → Set
Eternal-Env ⌊ St ⌋              = ⊤
Eternal-Env (∅ᵉ St)              = ⊤
Eternal-Env (reachᵉ γ q)        = Eternal-Env γ
Eternal-Env (γ ⟨ q ⟩ᵉ)           = Eternal-Env γ
Eternal-Env (γ ∷ᵉ V)            = Eternal-Env γ
Eternal-Env (liftᵉ V γ)         = Eternal-Env γ
Eternal-Env (eternalˡ Δ lf η γ) =
  Eternal-Env γ × (∀ {A ρ} → A ∈[ ρ ] Δ → Eternal A)

Rel-Env-eternal : ∀ {St Γ} → (γ : Env St Γ) → Rel-Env γ → Eternal-Env γ
Rel-Env-eternal ⌊ St ⌋              pγ        = tt
Rel-Env-eternal (∅ᵉ St)              pγ        = tt
Rel-Env-eternal (reachᵉ γ q)        pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (γ ⟨ q ⟩ᵉ)           pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (γ ∷ᵉ V)            (pγ , _)  = Rel-Env-eternal γ pγ
Rel-Env-eternal (liftᵉ V γ)         (pγ , _)  = Rel-Env-eternal γ pγ
Rel-Env-eternal (eternalˡ Δ lf η γ) (pγ , et) = Rel-Env-eternal γ pγ , et

