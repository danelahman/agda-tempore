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

-- RETYPING ALONG A CONTEXT EQUALITY

castᵛ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A
castᵛ refl V = V

castᶜ : ∀ {Γ Γ' C} → Γ ≡ Γ' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C
castᶜ refl M = M

------------------------------------------------------------------------
-- THE ACTION
--
-- Iterated single substitutions. Two things make it go through with only the
-- cut substitution `_[_↦_]c` the formalisation has:
--
--   * a value of the environment lives over `toCtx St`, while the cut needs it
--     over the context *left of* the variable it replaces — so it is first
--     weakened along the renaming the environment itself induces (`env-wk`);
--
--   * the variable to replace sits under whatever the recursion has already
--     passed, so the action is defined under an arbitrary *suffix* `Δ`. A lock
--     is absorbed into that suffix (`(Γ ⟨ ρ ⟩) ++ᶜ Δ ≡ Γ ++ᶜ ([] ⟨ ρ ⟩ ++ᶜ Δ)`),
--     which is what lets the substitution cross it: crossing is the
--     grade-lowering case of `⟨_,_⟩[_↦_]var`, licensed by the `var` rule's own
--     premise, and needs nothing from here.
------------------------------------------------------------------------

postulate

  -- THE ETERNAL ZONE. A closed eternal-typed value has to be weakened into the
  -- prefix it is substituted at; `Γ ᴱ` is lock-free, so this is iterated
  -- `wk-ren` off `Ren [] (Γ ᴱ)` — but `Ren [] Γ` is *not* available for a `Γ`
  -- with locks, so the lock-freeness has to be carried. Left as the one
  -- outstanding piece of the action.

  eternal-wk : ∀ {Δ Γ} → ClosedVals Δ → Ren Γ (Δ ++ᶜ Γ)

  env-eternal-V : ∀ {Δ Γ A} → ClosedVals Δ → (Δ ++ᶜ Γ) ⊢V⦂ A → Γ ⊢V⦂ A
  env-eternal-C : ∀ {Δ Γ C} → ClosedVals Δ → (Δ ++ᶜ Γ) ⊢C⦂ C → Γ ⊢C⦂ C

-- The renaming an environment induces: its values live over `toCtx St`, and
-- this puts them where the cut needs them. Locks are matched on both sides, so
-- they are pure congruence — the delicate lock-crossing is the substitution's,
-- not the renaming's.

env-wk : ∀ {St Γ} → (γ : Env St Γ) → Ren (toCtx St) Γ
env-wk ⌊ St ⌋            = id-ren
env-wk (γ ⟨ ρ ⟩ᵉ)         = cong-⟨⟩-ren (env-wk γ)
env-wk (γ ∷ᵉ V)          = wk-ren ∘ʳ env-wk γ
env-wk (eternalˡ Δ η γ)  = eternal-wk η ∘ʳ env-wk γ

-- The action under a suffix.

env-Vˢ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢V⦂ A
       → (toCtx St ++ᶜ Δ) ⊢V⦂ A

env-Cˢ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢C⦂ C
       → (toCtx St ++ᶜ Δ) ⊢C⦂ C

env-Vˢ ⌊ St ⌋ Δ V = V
env-Vˢ (_⟨_⟩ᵉ {St = St₀} {Γ = Γ} γ ρ) Δ V =
  castᵛ (sym (++ᶜ-assoc (toCtx St₀) ([] ⟨ ρ ⟩) Δ))
    (env-Vˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
      (castᵛ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) V))
env-Vˢ (_∷ᵉ_ {Γ = Γ} {A = A} γ W) Δ V =
  env-Vˢ γ Δ
    (castᵛ (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
      (V [ split→∈ s ↦ castᵛ (sym (split→∈-split-l s)) (V-rename (env-wk γ) W) ]v))
  where
    s = split-≡-++ᶜ {Γ ∷ A} {Δ}
env-Vˢ (eternalˡ Δ₀ η γ) Δ V =
  env-Vˢ γ Δ (env-eternal-V η (castᵛ (++ᶜ-assoc Δ₀ _ Δ) V))

env-Cˢ ⌊ St ⌋ Δ M = M
env-Cˢ (_⟨_⟩ᵉ {St = St₀} {Γ = Γ} γ ρ) Δ M =
  castᶜ (sym (++ᶜ-assoc (toCtx St₀) ([] ⟨ ρ ⟩) Δ))
    (env-Cˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
      (castᶜ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) M))
env-Cˢ (_∷ᵉ_ {Γ = Γ} {A = A} γ W) Δ M =
  env-Cˢ γ Δ
    (castᶜ (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
      (M [ split→∈ s ↦ castᵛ (sym (split→∈-split-l s)) (V-rename (env-wk γ) W) ]c))
  where
    s = split-≡-++ᶜ {Γ ∷ A} {Δ}
env-Cˢ (eternalˡ Δ₀ η γ) Δ M =
  env-Cˢ γ Δ (env-eternal-C η (castᶜ (++ᶜ-assoc Δ₀ _ Δ) M))

-- The action, at the empty suffix.

env-V : ∀ {St Γ A} → Env St Γ → Γ ⊢V⦂ A → toCtx St ⊢V⦂ A
env-V γ V = env-Vˢ γ [] V

env-C : ∀ {St Γ C} → Env St Γ → Γ ⊢C⦂ C → toCtx St ⊢C⦂ C
env-C γ M = env-Cˢ γ [] M

-- The state's own environment acts trivially — by definition.

env-V-id : ∀ {St A} → (V : toCtx St ⊢V⦂ A) → env-V ⌊ St ⌋ V ≡ V
env-V-id V = refl

env-C-id : ∀ {St C} → (M : toCtx St ⊢C⦂ C) → env-C ⌊ St ⌋ M ≡ M
env-C-id M = refl

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

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
