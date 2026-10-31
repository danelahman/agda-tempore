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

data Env : (𝕊 : State []) → Ctx → Set where

  ⌊_⌋      : (𝕊 : State [])
           ------------------
           → Env 𝕊 (toCtx 𝕊)

  -- Postcomposition with a reach: what makes `Env` functorial in the state.

  reachᵉ   : ∀ {𝕊 𝕊' Γ}
           → Env 𝕊 Γ → 𝕊 ⊑ₛ[ 𝟏ᵣ ] 𝕊'
           ------------------------------
           → Env 𝕊' Γ

  -- a lock, matched by any state far enough ahead

  _⟨_⟩ᵉ    : ∀ {𝕊 𝕊' Γ ρ}
           → Env 𝕊 Γ → 𝕊 ⊑ₛ[ ρ ] 𝕊'
           ------------------------------
           → Env 𝕊' (Γ ⟨ ρ ⟩)

  _∷ᵉ_     : ∀ {𝕊 Γ A}
           → Env 𝕊 Γ → toCtx 𝕊 ⊢V⦂ A
           ---------------------------
           → Env 𝕊 (Γ ∷ A)

  -- A binder matched by a freshly allocated cell, as `BOX` steps
  -- `⟨ 𝕊 ∣ box V M ⟩ ⟶ ⟨ 𝕊 ∷ₛ V' ∣ M ⟩`; acts as `γ` under the suffix
  -- `[] ∷ [ ρ ] A`.

  liftᵉ    : ∀ {𝕊 Γ A ρ}
           → (V : ([] ++ᶜ toCtx 𝕊 ⟨ ρ ⟩) ⊢V⦂ A) → Env 𝕊 Γ
           ------------------------------------------------
           → Env (𝕊 ∷ₛ V) (Γ ∷ [ ρ ] A)

-- The state's own part is the store; each instantiated binder holds a
-- reducible value.

Rel-Env : ∀ {𝕊 Γ} → Env 𝕊 Γ → Set
Rel-Env ⌊ 𝕊 ⌋                 = SRed 𝕊
Rel-Env (γ ⟨ q ⟩ᵉ)             = Rel-Env γ
Rel-Env (_∷ᵉ_ {𝕊} {Γ} {A} γ V) = Rel-Env γ × VRed A 𝕊 V
Rel-Env (liftᵉ {𝕊} {Γ} {A} {ρ} V γ) =
  Rel-Env γ
  × (∀ {𝕊'} → (q : 𝕊 ⊑ₛ[ ρ ] 𝕊')
       → VRed A 𝕊' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V))
Rel-Env (reachᵉ γ q)           = Rel-Env γ

