------------------------------------------------------------------------
-- Closing environments over a state.                                   --
--                                                                    --
-- The formalisation has only *cut-style single-variable* substitution   --
-- (`Syntax.Substitutions`), so a closing environment is not a `Sub`: it --
-- is a description of how a context is built from a state, to be        --
-- realised by iterated innermost-first single substitutions (route (b)   --
-- of `notes/adequacy-plan.md`).                                          --
--                                                                    --
-- The three zones a context of the fundamental lemma has:                --
--                                                                    --
--   * `⌊ St ⌋`      — the state itself: locks and cells, closed by the    --
--                     store (its resource variables are its own);         --
--   * `_∷ᵉ_`/`_⟨_⟩ᵉ` — the binder telescope on the right, each ordinary   --
--                     variable instantiated by a value over `toCtx St`,   --
--                     each lock matched by a lock on the state;           --
--   * `eternalˡ`    — an eternal prefix on the left, as handler clauses    --
--                     close over `Γ ᴱ` and are instantiated at            --
--                     `Γ' := toCtx St` in the middle (`HANDLE-OP`).       --
--                     `toCtx St ᴱ ≡ []`, so eternal-typed values over a    --
--                     state context are closed.                           --
------------------------------------------------------------------------

open import Data.Product
open import Data.Unit using (⊤; tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Environment (Spec : LanguageSpec) where

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

open import OperationalSemantics.Adequacy.Reducibility Spec
open import OperationalSemantics.Adequacy.Slice        Spec

-- Closed values for an eternal prefix.

ClosedVals : Ctx → Set
ClosedVals Δ = ∀ {A ρ} → A ∈[ ρ ] Δ → [] ⊢V⦂ A

-- A closing environment: how `Γ` is closed down to the state context.

infixl 30 _∷ᵉ_
infix  32 _⟨_⟩ᵉ

data Env : (St : 𝕊 []) → Ctx → Set where

  ⌊_⌋      : (St : 𝕊 [])
           ------------------
           → Env St (toCtx St)

  _⟨_⟩ᵉ    : ∀ {St Γ}
           → Env St Γ → (ρ : R)
           ---------------------------
           → Env (St ⟨ ρ ⟩ₛ) (Γ ⟨ ρ ⟩)

  _∷ᵉ_     : ∀ {St Γ A}
           → Env St Γ → toCtx St ⊢V⦂ A
           ---------------------------
           → Env St (Γ ∷ A)

  eternalˡ : ∀ {St Γ}
           → (Δ : Ctx) → ClosedVals Δ → Env St Γ
           -------------------------------------
           → Env St (Δ ++ᶜ Γ)

-- REDUCIBLE ENVIRONMENTS
--
-- The state's own part is the store; each instantiated binder holds a
-- reducible value; the eternal prefix holds closed constants, of which nothing
-- is asked (eternal types are base/unit/products).

Rel-Env : ∀ {St Γ} → Env St Γ → Set
Rel-Env ⌊ St ⌋                = Store St
Rel-Env (γ ⟨ ρ ⟩ᵉ)             = Rel-Env γ
Rel-Env (_∷ᵉ_ {St} {Γ} {A} γ V) = Rel-Env γ × Val A St V
Rel-Env (eternalˡ Δ η γ)       = Rel-Env γ

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- THE ACTION. Built as iterated single substitutions: innermost binder
  -- first, values entering from the left of the variable they replace (the
  -- `split-l` discipline of `_[_↦_]v`/`_[_↦_]c`). Crossing a lock is the
  -- grade-lowering case of `⟨_,_⟩[_↦_]var`, licensed by the `var` rule's own
  -- premise; eternal data crosses unconditionally (`eternal-val-ext`).

  env-V : ∀ {St Γ A} → Env St Γ → Γ ⊢V⦂ A → toCtx St ⊢V⦂ A
  env-C : ∀ {St Γ C} → Env St Γ → Γ ⊢C⦂ C → toCtx St ⊢C⦂ C

  -- The state's own environment acts trivially.

  env-V-id : ∀ {St A} → (V : toCtx St ⊢V⦂ A) → env-V ⌊ St ⌋ V ≡ V
  env-C-id : ∀ {St C} → (M : toCtx St ⊢C⦂ C) → env-C ⌊ St ⌋ M ≡ M

  -- Instantiating a binder is substituting into the closed body: the law the
  -- `lam`/`_·_` case of the fundamental lemma needs. (The action's remaining
  -- commutation laws — one per term former — come with its construction.)

  env-lam : ∀ {St Γ A B ε} → (γ : Env St Γ) → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
          → Σ[ M' ∈ toCtx St ∷ A ⊢C⦂ B ‼ ε ]
              (env-V γ (lam M) ≡ lam M')
            × (∀ (W : toCtx St ⊢V⦂ A) → M' [ Hd ↦ W ]c ≡ env-C (γ ∷ᵉ W) M)

  -- A value's eternal restriction is closed over a state context, which is
  -- what lets a handler clause's `Γ ᴱ` zone be instantiated (`HANDLE-OP`
  -- fires at `Γ' := toCtx St`, and `toCtxᴱ-[]` empties the state's own
  -- eternal part).

  env-ᴱ : ∀ {St Γ} → (γ : Env St Γ) → Rel-Env γ → ClosedVals (Γ ᴱ)
