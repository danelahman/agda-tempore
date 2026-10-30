------------------------------------------------------------------------
-- Closing environments: `Env` and its reducibility predicate.
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (yes; no; ¬_; Dec)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Termination.Environment.Core (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec

open import MonomorphicCalculus.Syntax.Contexts        Spec
open import MonomorphicCalculus.Syntax.Terms           Spec
open import MonomorphicCalculus.Syntax.Renaming.Action Spec
open import MonomorphicCalculus.Syntax.Renaming        Spec
open import MonomorphicCalculus.Syntax.Substitution    Spec
open import MonomorphicCalculus.Syntax.Types           Spec

open import MonomorphicCalculus.OperationalSemantics.Termination.Reducibility Spec
open import MonomorphicCalculus.Syntax.Renaming.Equivalence  Spec
open import MonomorphicCalculus.Syntax.Renaming.Coherence    Spec
open import MonomorphicCalculus.Syntax.Terms.Equivalence     Spec
open import MonomorphicCalculus.Syntax.Terms.Transport       Spec
open import MonomorphicCalculus.Syntax.Substitution.Variables  Spec
open import MonomorphicCalculus.Syntax.Substitution.At         Spec
open import MonomorphicCalculus.Syntax.Substitution.Clauses    Spec
open import MonomorphicCalculus.OperationalSemantics.GradedReach Spec
open import MonomorphicCalculus.Syntax.Substitution.Equivalence  Spec

-- A closing environment: how `Γ` is closed down to the state context.

infixl 30 _∷ᵉ_
infix  32 _⟨_⟩ᵉ

data Env : (St : 𝕊 []) → Ctx → Set where

  ⌊_⌋      : (St : 𝕊 [])
           ------------------
           → Env St (toCtx St)

  -- Postcomposition with a reach: what makes `Env` functorial in the state.

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

  -- A binder matched by a freshly allocated cell, as `BOX` steps
  -- `⟨St, box V M⟩ ↝ ⟨St ∷ₛ V', M⟩`; acts as `γ` under the suffix
  -- `[] ∷ [ ρ ] A`.

  liftᵉ    : ∀ {St Γ A ρ}
           → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A) → Env St Γ
           ------------------------------------------------
           → Env (St ∷ₛ V) (Γ ∷ [ ρ ] A)

-- The state's own part is the store; each instantiated binder holds a
-- reducible value.

Rel-Env : ∀ {St Γ} → Env St Γ → Set
Rel-Env ⌊ St ⌋                = SRed St
Rel-Env (γ ⟨ q ⟩ᵉ)             = Rel-Env γ
Rel-Env (_∷ᵉ_ {St} {Γ} {A} γ V) = Rel-Env γ × VRed A St V
Rel-Env (liftᵉ {St} {Γ} {A} {ρ} V γ) =
  Rel-Env γ
  × (∀ {St'} → (q : St ⊑ₛ[ ρ ] St')
       → VRed A St' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V))
Rel-Env (reachᵉ γ q)           = Rel-Env γ

