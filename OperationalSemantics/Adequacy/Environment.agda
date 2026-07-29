------------------------------------------------------------------------
-- Closing environments over a state.                                 --
--                                                                    --
-- `Syntax.Substitutions` provides single-variable substitution whose --
-- replacement is *prefix-typed*: typed in the context left of the    --
-- variable it replaces, which the substitution removes. A closing    --
-- environment is therefore not a `Sub` but a description of how a    --
-- context is built from a state, realised by iterated single         --
-- substitutions.                                                     --
--                                                                    --
-- The zones a context of the fundamental lemma has:                  --
--                                                                    --
--   * `⌊ St ⌋`  — the state: locks and cells, closed by the store;   --
--   * `_∷ᵉ_`/`_⟨_⟩ᵉ` — the binder telescope: each variable           --
--                 instantiated by a value, each lock matched by a    --
--                 slice into a state far enough ahead;               --
--   * `eternalˡ` — an eternal prefix: handler clauses close over     --
--                 `Γ ᴱ` and fire at `Γ' := toCtx St` (`HANDLE-OP`);  --
--                 `toCtx St ᴱ ≡ []`, so eternal values are closed.   --
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

open import OperationalSemantics.Adequacy.Reducibility   Spec
open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import Syntax.Substitutions.Weakening Spec
open import Syntax.Substitutions.Renaming  Spec
open import Syntax.Substitutions.Swap      Spec
open import OperationalSemantics.Adequacy.Slice          Spec
open import Syntax.Substitutions.Equivalence Spec

-- Closed values for an eternal prefix.

ClosedVals : Ctx → Set
ClosedVals Δ = ∀ {A ρ} → A ∈[ ρ ] Δ → [] ⊢V⦂ A

-- LOCK-FREE CONTEXTS
--
-- `_ᴱ` drops every lock, so the eternal prefix is lock-free — which is what
-- makes a closed value weakenable into it: `Ren [] [] Γ` exists exactly when `Γ`
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

empty-ren : ∀ {Δ} → Lock-free Δ → Ren [] [] Δ
empty-ren lf-[]     = id-ren
empty-ren (lf-∷ lf) = wk-ren ∘ʳ empty-ren lf

eternal-wk : ∀ {Δ} → Lock-free Δ → (Γ : Ctx) → Ren [] Γ (Δ ++ᶜ Γ)
eternal-wk lf []        = empty-ren lf
eternal-wk lf (Γ ∷ A)   = cong-∷-ren (eternal-wk lf Γ)
eternal-wk lf (Γ ⟨ ρ ⟩) = cong-⟨⟩-ren (eternal-wk lf Γ)

-- Weakening a *closed* term into a state's context. Locks are crossed by
-- `⟨⟩-ext-ctx`, which asks for everything to their left to be eternal — and here
-- that is `[]`, vacuously. Which such renaming is chosen never matters: `_≐ʳ_`
-- compares renamings on variables, and `[]` has none (`∅-ren-≐`).

∅-ren : (St : 𝕊 []) → Ren [] [] (toCtx St)
∅-ren St = wk-ctx-ren ec-[] (toCtx St)

∅-ren-≐ : ∀ {Γ} → (r r' : Ren [] [] Γ) → r ≐ʳ r'
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

  -- postcomposition with a slice: what makes `Env` functorial in the *state*
  -- (`env-alloc`). Recorded rather than pushed into the base, so that a
  -- reducible environment stays reducible when the state grows: its values
  -- still come from the earlier state, and `Val-slice` moves them. Pushing it
  -- into `⌊_⌋` would instead demand the *later* state's store, which nothing
  -- supplies.

  sliceᵉ   : ∀ {St St' Γ}
           → Env St Γ → Slice St uᵣ St' uᵣ
           ------------------------------
           → Env St' Γ

  -- a lock, matched by any state far enough ahead

  _⟨_⟩ᵉ    : ∀ {St St' Γ ρ}
           → Env St Γ → Slice St ρ St' uᵣ
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
  × (∀ {St'} → (q : Slice St ρ St' uᵣ)
       → Val A St' (V-rename (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ) V))
Rel-Env (sliceᵉ γ q)           = Rel-Env γ
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
Eternal-Env (sliceᵉ γ q)        = Eternal-Env γ
Eternal-Env (γ ⟨ q ⟩ᵉ)           = Eternal-Env γ
Eternal-Env (γ ∷ᵉ V)            = Eternal-Env γ
Eternal-Env (liftᵉ V γ)         = Eternal-Env γ
Eternal-Env (eternalˡ Δ lf η γ) =
  Eternal-Env γ × (∀ {A ρ} → A ∈[ ρ ] Δ → Eternal A)

Rel-Env-eternal : ∀ {St Γ} → (γ : Env St Γ) → Rel-Env γ → Eternal-Env γ
Rel-Env-eternal ⌊ St ⌋              pγ        = tt
Rel-Env-eternal (∅ᵉ St)              pγ        = tt
Rel-Env-eternal (sliceᵉ γ q)        pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (γ ⟨ q ⟩ᵉ)           pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (γ ∷ᵉ V)            (pγ , _)  = Rel-Env-eternal γ pγ
Rel-Env-eternal (liftᵉ V γ)         (pγ , _)  = Rel-Env-eternal γ pγ
Rel-Env-eternal (eternalˡ Δ lf η γ) (pγ , et) = Rel-Env-eternal γ pγ , et


------------------------------------------------------------------------
-- THE ACTION
--
-- Iterated single substitutions. Two things make it go through with only the
-- prefix-typed substitution `_[_↦_]c` the formalisation has:
--
--   * the variable to replace sits under whatever the recursion has already
--     passed, so the action is defined under an arbitrary *suffix* `Δ`. A lock
--     is absorbed into that suffix (`(Γ ⟨ ρ ⟩) ++ᶜ Δ ≡ Γ ++ᶜ ([] ⟨ ρ ⟩ ++ᶜ Δ)`),
--     which is what lets the substitution cross it: crossing is the
--     grade-lowering case of `⟨_,_⟩[_↦_]var`, licensed by the `var` rule's own
--     premise, and needs nothing from here;
--
--   * a telescope entry is substituted *last*: it rides along in the suffix
--     (`[] ∷ A ++ᶜ Δ`) and its variable is substituted afterwards. Its value
--     already lives over the prefix `toCtx St`, so it needs no weakening, and
--     `env-C (γ ∷ᵉ W) M ≡ (env-Cˢ γ ([] ∷ A) M) [ Hd ↦ W ]c` holds
--     definitionally — the order `APP` wants.
------------------------------------------------------------------------

-- THE ETERNAL ZONE
--
-- Substitute each prefix variable by its closed value, outermost first, each
-- weakened into the prefix left of the variable it replaces (`empty-ren`).

env-eternal-V : ∀ {Δ Γ A} → Lock-free Δ → ClosedVals Δ
              → (Δ ++ᶜ Γ) ⊢V⦂ A → Γ ⊢V⦂ A
env-eternal-V lf-[] η V = castᵛ ++ᶜ-identityˡ V
env-eternal-V {Δ ∷ B} {Γ} (lf-∷ lf) η V =
  env-eternal-V lf (λ x → η (Tl-∷ x))
    (castᵛ (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
      (V [ split→∈ s ↦ castᵛ (sym (split→∈-split-l s))
                         (V-rename (empty-ren lf) (η Hd)) ]v))
  where
    s = split-≡-++ᶜ {Δ ∷ B} {Γ}

env-eternal-C : ∀ {Δ Γ C} → Lock-free Δ → ClosedVals Δ
              → (Δ ++ᶜ Γ) ⊢C⦂ C → Γ ⊢C⦂ C
env-eternal-C lf-[] η M = castᶜ ++ᶜ-identityˡ M
env-eternal-C {Δ ∷ B} {Γ} (lf-∷ lf) η M =
  env-eternal-C lf (λ x → η (Tl-∷ x))
    (castᶜ (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
      (M [ split→∈ s ↦ castᵛ (sym (split→∈-split-l s))
                         (V-rename (empty-ren lf) (η Hd)) ]c))
  where
    s = split-≡-++ᶜ {Δ ∷ B} {Γ}

-- The action under a suffix.

env-Vˢ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢V⦂ A
       → (toCtx St ++ᶜ Δ) ⊢V⦂ A

env-Cˢ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
       → (Γ ++ᶜ Δ) ⊢C⦂ C
       → (toCtx St ++ᶜ Δ) ⊢C⦂ C

env-Vˢ ⌊ St ⌋ Δ V = V
env-Vˢ (∅ᵉ St) Δ V = V-rename (cong-ren (∅-ren St)) V
env-Vˢ (sliceᵉ γ q) Δ V = V-rename (cong-ren (slice-renᵘ q)) (env-Vˢ γ Δ V)
env-Vˢ (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  V-rename (cong-ren (unbox-ren q))
    (castᵛ (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))
      (env-Vˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
        (castᵛ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) V)))
env-Vˢ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ V =
  castᵛ (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    ((castᵛ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
       (env-Vˢ γ ([] ∷ A ++ᶜ Δ) (castᵛ (++ᶜ-assoc Γ ([] ∷ A) Δ) V)))
      [ split→∈ t ↦ castᵛ (sym (split→∈-split-l t)) W ]v)
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}
env-Vˢ (liftᵉ {St = St} {Γ = Γ} {A = A} {ρ = ρ} V γ) Δ V₀ =
  castᵛ (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))
    (env-Vˢ γ ([] ∷ [ ρ ] A ++ᶜ Δ)
      (castᵛ (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) V₀))
env-Vˢ (eternalˡ Δ₀ lf η γ) Δ V =
  env-Vˢ γ Δ (env-eternal-V lf η (castᵛ (++ᶜ-assoc Δ₀ _ Δ) V))

env-Cˢ ⌊ St ⌋ Δ M = M
env-Cˢ (∅ᵉ St) Δ M = C-rename (cong-ren (∅-ren St)) M
env-Cˢ (sliceᵉ γ q) Δ M = C-rename (cong-ren (slice-renᵘ q)) (env-Cˢ γ Δ M)
env-Cˢ (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  C-rename (cong-ren (unbox-ren q))
    (castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))
      (env-Cˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
        (castᶜ (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) M)))
env-Cˢ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ M =
  castᶜ (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    ((castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
       (env-Cˢ γ ([] ∷ A ++ᶜ Δ) (castᶜ (++ᶜ-assoc Γ ([] ∷ A) Δ) M)))
      [ split→∈ t ↦ castᵛ (sym (split→∈-split-l t)) W ]c)
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}
env-Cˢ (liftᵉ {St = St} {Γ = Γ} {A = A} {ρ = ρ} V γ) Δ M =
  castᶜ (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))
    (env-Cˢ γ ([] ∷ [ ρ ] A ++ᶜ Δ)
      (castᶜ (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) M))
env-Cˢ (eternalˡ Δ₀ lf η γ) Δ M =
  env-Cˢ γ Δ (env-eternal-C lf η (castᶜ (++ᶜ-assoc Δ₀ _ Δ) M))

-- THE ACTION COMMUTES WITH `lam`
--
-- Each single substitution does, and the variable substituted at suffix
-- `Δ ∷ A` is `Tl-∷` of the one at `Δ` — definitionally, since `split-≡-++ᶜ` is
-- `≡-split refl` and `≡-split` recurses on the suffix. Only the casts differ.

env-eternal-lam : ∀ {Δ Γ A B ε} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (M : (Δ ++ᶜ Γ) ∷ A ⊢C⦂ B ‼ ε)
                → env-eternal-V lf η (lam M) ≡ lam (env-eternal-C lf η M)

env-eternal-lam {A = A} lf-[] η M =
  trans (cast-lam ++ᶜ-identityˡ M)
        (cong lam (castᶜ-irr (cong (_∷ A) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))

env-eternal-lam {Δ ∷ B} {Γ} {A} (lf-∷ lf) η M =
  begin
    env-eternal-V lf η' (castᵛ e (lam body))
  ≡⟨ cong (env-eternal-V lf η') (cast-lam e body) ⟩
    env-eternal-V lf η' (lam (castᶜ (cong (_∷ A) e) body))
  ≡⟨ env-eternal-lam lf η' (castᶜ (cong (_∷ A) e) body) ⟩
    lam (env-eternal-C lf η' (castᶜ (cong (_∷ A) e) body))
  ≡⟨ cong (λ z → lam (env-eternal-C lf η' z))
          (castᶜ-irr (cong (_∷ A) e) e' body) ⟩
    lam (env-eternal-C lf η' (castᶜ e' body))
  ∎
  where
    η'   = λ {A' ρ'} (x : A' ∈[ ρ' ] Δ) → η (Tl-∷ x)
    s    = split-≡-++ᶜ {Δ ∷ B} {Γ}
    s'   = split-≡-++ᶜ {Δ ∷ B} {Γ ∷ A}
    Ŵ    = castᵛ (sym (split→∈-split-l s)) (V-rename (empty-ren lf) (η Hd))
    body = M [ Tl-∷ (split→∈ s) ↦ Ŵ ]c
    e    = cong₂ _++ᶜ_ (split→∈-split-l s)  (split→∈-split-r s)
    e'   = cong₂ _++ᶜ_ (split→∈-split-l s') (split→∈-split-r s')

env-Vˢ-lam : ∀ {St Γ A B ε} → (γ : Env St Γ) → (Δ : Ctx)
           → (M : (Γ ++ᶜ Δ) ∷ A ⊢C⦂ B ‼ ε)
           → env-Vˢ γ Δ (lam M) ≡ lam (env-Cˢ γ (Δ ∷ A) M)

env-Vˢ-lam ⌊ St ⌋ Δ M = refl
env-Vˢ-lam (∅ᵉ St) Δ M = refl
env-Vˢ-lam (sliceᵉ γ q) Δ M = cong (V-rename (cong-ren (slice-renᵘ q))) (env-Vˢ-lam γ Δ M)

env-Vˢ-lam {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (lam M)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-lam ei M) ⟩
      castᵛ eo (env-Vˢ γ Δ' (lam (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-lam γ Δ' (castᶜ (cong (_∷ A) ei) M)) ⟩
      castᵛ eo (lam (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cast-lam eo _ ⟩
      lam (castᶜ (cong (_∷ A) eo) (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cong lam (castᶜ-irr (cong (_∷ A) eo) eo' _) ⟩
      lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
    ≡⟨ cong (λ z → lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) z)))
            (castᶜ-irr (cong (_∷ A) ei) ei' M) ⟩
      lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ ei' M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo' = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ A))
    ei' = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ A)

env-Vˢ-lam {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ M =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (lam M)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-lam ei M) ⟩
    castᵛ eo (env-Vˢ γ Δ' (lam (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-lam γ Δ' (castᶜ (cong (_∷ A) ei) M)) ⟩
    castᵛ eo (lam (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cast-lam eo _ ⟩
    lam (castᶜ (cong (_∷ A) eo) (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cong lam (castᶜ-irr (cong (_∷ A) eo) eo' _) ⟩
    lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ (cong (_∷ A) ei) M)))
  ≡⟨ cong (λ z → lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) z)))
          (castᶜ-irr (cong (_∷ A) ei) ei' M) ⟩
    lam (castᶜ eo' (env-Cˢ γ (Δ' ∷ A) (castᶜ ei' M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo' = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ A))
    ei' = ++ᶜ-assoc Γ Δ₁ (Δ ∷ A)

env-Vˢ-lam {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (lam M)))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ z)) [ x ↦ Ŵ ]v))
          (cast-lam eA M) ⟩
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (lam (castᶜ (cong (_∷ A) eA) M))))
                  [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn z) [ x ↦ Ŵ ]v))
          (env-Vˢ-lam γ Δ₁ (castᶜ (cong (_∷ A) eA) M)) ⟩
    castᵛ eOut ((castᵛ eIn (lam body)) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut (z [ x ↦ Ŵ ]v)) (cast-lam eIn body) ⟩
    castᵛ eOut ((lam (castᶜ (cong (_∷ A) eIn) body)) [ x ↦ Ŵ ]v)
  ≡⟨ cast-lam eOut ((castᶜ (cong (_∷ A) eIn) body) [ Tl-∷ x ↦ Ŵ ]c) ⟩
    lam (castᶜ (cong (_∷ A) eOut)
           ((castᶜ (cong (_∷ A) eIn) body) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong lam (castᶜ-irr (cong (_∷ A) eOut) eOut'
                 ((castᶜ (cong (_∷ A) eIn) body) [ Tl-∷ x ↦ Ŵ ]c)) ⟩
    lam (castᶜ eOut' ((castᶜ (cong (_∷ A) eIn) body) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → lam (castᶜ eOut' (z [ Tl-∷ x ↦ Ŵ ]c)))
          (castᶜ-irr (cong (_∷ A) eIn) eIn' body) ⟩
    lam (castᶜ eOut' ((castᶜ eIn' body) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → lam (castᶜ eOut'
             ((castᶜ eIn' (env-Cˢ γ (Δ₁ ∷ A) z)) [ Tl-∷ x ↦ Ŵ ]c)))
          (castᶜ-irr (cong (_∷ A) eA) eA' M) ⟩
    lam (castᶜ eOut' ((castᶜ eIn' (env-Cˢ γ (Δ₁ ∷ A) (castᶜ eA' M)))
                        [ Tl-∷ x ↦ Ŵ ]c))
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    t     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t'    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ∷ A}
    x     = split→∈ t
    Ŵ     = castᵛ (sym (split→∈-split-l t)) W
    eOut  = cong₂ _++ᶜ_ (split→∈-split-l t)  (split→∈-split-r t)
    eOut' = cong₂ _++ᶜ_ (split→∈-split-l t') (split→∈-split-r t')
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn'  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA'   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ A)
    body  = env-Cˢ γ (Δ₁ ∷ A) (castᶜ (cong (_∷ A) eA) M)

env-Vˢ-lam {A = A} (eternalˡ Δ₀ lf η γ) Δ M =
  begin
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e (lam M)))
  ≡⟨ cong (λ z → env-Vˢ γ Δ (env-eternal-V lf η z)) (cast-lam e M) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (lam (castᶜ (cong (_∷ A) e) M)))
  ≡⟨ cong (env-Vˢ γ Δ) (env-eternal-lam lf η (castᶜ (cong (_∷ A) e) M)) ⟩
    env-Vˢ γ Δ (lam (env-eternal-C lf η (castᶜ (cong (_∷ A) e) M)))
  ≡⟨ env-Vˢ-lam γ Δ (env-eternal-C lf η (castᶜ (cong (_∷ A) e) M)) ⟩
    lam (env-Cˢ γ (Δ ∷ A) (env-eternal-C lf η (castᶜ (cong (_∷ A) e) M)))
  ≡⟨ cong (λ z → lam (env-Cˢ γ (Δ ∷ A) (env-eternal-C lf η z)))
          (castᶜ-irr (cong (_∷ A) e) e' M) ⟩
    lam (env-Cˢ γ (Δ ∷ A) (env-eternal-C lf η (castᶜ e' M)))
  ∎
  where
    e  = ++ᶜ-assoc Δ₀ _ Δ
    e' = ++ᶜ-assoc Δ₀ _ (Δ ∷ A)

-- THE ACTION COMMUTES WITH THE NON-BINDING FORMERS
--
-- The suffix does not grow, so both sides carry the same cast proofs and no
-- `castᶜ-irr` step is needed.

env-eternal-const : ∀ {Δ Γ b} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                  → (c : BaseConstants b)
                  → env-eternal-V {Γ = Γ} lf η (const c) ≡ const c
env-eternal-const lf-[]     η c = cast-const ++ᶜ-identityˡ
env-eternal-const (lf-∷ lf) η c =
  trans (cong (env-eternal-V lf _) (cast-const _))
        (env-eternal-const lf _ c)

env-eternal-⋆ : ∀ {Δ Γ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
              → env-eternal-V {Γ = Γ} lf η ⋆ ≡ ⋆
env-eternal-⋆ lf-[]     η = cast-⋆ ++ᶜ-identityˡ
env-eternal-⋆ (lf-∷ lf) η =
  trans (cong (env-eternal-V lf _) (cast-⋆ _)) (env-eternal-⋆ lf _)

env-eternal-pair : ∀ {Δ Γ A B} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                 → (V : (Δ ++ᶜ Γ) ⊢V⦂ A) → (W : (Δ ++ᶜ Γ) ⊢V⦂ B)
                 → env-eternal-V lf η ⦉ V , W ⦊
                 ≡ ⦉ env-eternal-V lf η V , env-eternal-V lf η W ⦊
env-eternal-pair lf-[]     η V W = cast-pair ++ᶜ-identityˡ
env-eternal-pair (lf-∷ lf) η V W =
  trans (cong (env-eternal-V lf _) (cast-pair _))
        (env-eternal-pair lf _ _ _)

env-eternal-ret : ∀ {Δ Γ A} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ A)
                → env-eternal-C lf η (return V) ≡ return (env-eternal-V lf η V)
env-eternal-ret lf-[]     η V = cast-ret ++ᶜ-identityˡ
env-eternal-ret (lf-∷ lf) η V =
  trans (cong (env-eternal-C lf _) (cast-ret _)) (env-eternal-ret lf _ _)

env-eternal-app : ∀ {Δ Γ A C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ A ⇒ C) → (W : (Δ ++ᶜ Γ) ⊢V⦂ A)
                → env-eternal-C lf η (V · W)
                ≡ (env-eternal-V lf η V) · (env-eternal-V lf η W)
env-eternal-app lf-[]     η V W = cast-app ++ᶜ-identityˡ
env-eternal-app (lf-∷ lf) η V W =
  trans (cong (env-eternal-C lf _) (cast-app _)) (env-eternal-app lf _ _ _)

env-eternal-absurd : ∀ {Δ Γ C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                   → (V : (Δ ++ᶜ Γ) ⊢V⦂ Empty)
                   → env-eternal-C {C = C} lf η (absurd V)
                   ≡ absurd (env-eternal-V lf η V)
env-eternal-absurd lf-[]     η V = cast-absurd ++ᶜ-identityˡ
env-eternal-absurd (lf-∷ lf) η V =
  trans (cong (env-eternal-C lf _) (cast-absurd _))
        (env-eternal-absurd lf _ _)

env-eternal-coerce : ∀ {Δ Γ A ε ε'} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                   → {p : ε ≾ₑ ε'} → (M : (Δ ++ᶜ Γ) ⊢C⦂ A ‼ ε)
                   → env-eternal-C lf η (coerce p M)
                   ≡ coerce p (env-eternal-C lf η M)
env-eternal-coerce lf-[]     η M = cast-coerce ++ᶜ-identityˡ
env-eternal-coerce (lf-∷ lf) η M =
  trans (cong (env-eternal-C lf _) (cast-coerce _))
        (env-eternal-coerce lf _ _)

env-Cˢ-ret : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → (V : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Cˢ γ Δ (return V) ≡ return (env-Vˢ γ Δ V)

env-Cˢ-ret ⌊ St ⌋ Δ V = refl
env-Cˢ-ret (∅ᵉ St) Δ V = refl
env-Cˢ-ret (sliceᵉ γ q) Δ V = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-ret γ Δ V)

env-Cˢ-ret (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (return V)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-ret ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (return (castᵛ ei V)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-ret γ Δ' (castᵛ ei V)) ⟩
      castᶜ eo (return (env-Vˢ γ Δ' (castᵛ ei V)))
    ≡⟨ cast-ret eo ⟩
      return (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-ret (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (return V)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-ret ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (return (castᵛ ei V)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-ret γ Δ' (castᵛ ei V)) ⟩
    castᶜ eo (return (env-Vˢ γ Δ' (castᵛ ei V)))
  ≡⟨ cast-ret eo ⟩
    return (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-ret (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (return V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-ret eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (return (castᵛ eA V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
          (env-Cˢ-ret γ Δ₁ (castᵛ eA V)) ⟩
    castᶜ eOut ((castᶜ eIn (return (env-Vˢ γ Δ₁ (castᵛ eA V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-ret eIn) ⟩
    castᶜ eOut ((return (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-ret eOut ⟩
    return (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v))
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-ret (eternalˡ Δ₀ lf η γ) Δ V =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (return V)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-ret e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (return (castᵛ e V)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-ret lf η (castᵛ e V)) ⟩
    env-Cˢ γ Δ (return (env-eternal-V lf η (castᵛ e V)))
  ≡⟨ env-Cˢ-ret γ Δ (env-eternal-V lf η (castᵛ e V)) ⟩
    return (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Cˢ-app : ∀ {St Γ A C} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A ⇒ C) → (U : (Γ ++ᶜ Δ) ⊢V⦂ A)
           → env-Cˢ γ Δ (V · U) ≡ (env-Vˢ γ Δ V) · (env-Vˢ γ Δ U)

env-Cˢ-app ⌊ St ⌋ Δ V U = refl
env-Cˢ-app (∅ᵉ St) Δ V U = refl
env-Cˢ-app (sliceᵉ γ q) Δ V U = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-app γ Δ V U)

env-Cˢ-app (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V U =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (V · U)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-app ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (castᵛ ei V · castᵛ ei U))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-app γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
      castᶜ eo (env-Vˢ γ Δ' (castᵛ ei V) · env-Vˢ γ Δ' (castᵛ ei U))
    ≡⟨ cast-app eo ⟩
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) · castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-app (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V U =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (V · U)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-app ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (castᵛ ei V · castᵛ ei U))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-app γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
    castᶜ eo (env-Vˢ γ Δ' (castᵛ ei V) · env-Vˢ γ Δ' (castᵛ ei U))
  ≡⟨ cast-app eo ⟩
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) · castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-app (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V U =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (V · U)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-app eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᵛ eA V · castᵛ eA U))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c)) (env-Cˢ-app γ Δ₁ (castᵛ eA V) (castᵛ eA U)) ⟩
    castᶜ eOut ((castᶜ eIn (env-Vˢ γ Δ₁ (castᵛ eA V) · env-Vˢ γ Δ₁ (castᵛ eA U))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-app eIn) ⟩
    castᶜ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)) · castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-app eOut ⟩
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v) · castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) [ x ↦ Ŵ ]v)
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-app (eternalˡ Δ₀ lf η γ) Δ V U =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (V · U)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-app e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (castᵛ e V · castᵛ e U))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-app lf η (castᵛ e V) (castᵛ e U)) ⟩
    env-Cˢ γ Δ (env-eternal-V lf η (castᵛ e V) · env-eternal-V lf η (castᵛ e U))
  ≡⟨ env-Cˢ-app γ Δ (env-eternal-V lf η (castᵛ e V)) (env-eternal-V lf η (castᵛ e U)) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)) · env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e U))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Cˢ-absurd : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx)
              → (V : (Γ ++ᶜ Δ) ⊢V⦂ Empty)
              → env-Cˢ γ Δ (absurd {C = C} V) ≡ absurd (env-Vˢ γ Δ V)

env-Cˢ-absurd ⌊ St ⌋ Δ V = refl
env-Cˢ-absurd (∅ᵉ St) Δ V = refl
env-Cˢ-absurd (sliceᵉ γ q) Δ V = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-absurd γ Δ V)

env-Cˢ-absurd (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (absurd (V))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-absurd ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (absurd (castᵛ ei V)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-absurd γ Δ' (castᵛ ei V)) ⟩
      castᶜ eo (absurd (env-Vˢ γ Δ' (castᵛ ei V)))
    ≡⟨ cast-absurd eo ⟩
      absurd (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-absurd (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (absurd (V))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-absurd ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (absurd (castᵛ ei V)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-absurd γ Δ' (castᵛ ei V)) ⟩
    castᶜ eo (absurd (env-Vˢ γ Δ' (castᵛ ei V)))
  ≡⟨ cast-absurd eo ⟩
    absurd (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-absurd (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (absurd (V))))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-absurd eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (absurd (castᵛ eA V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c)) (env-Cˢ-absurd γ Δ₁ (castᵛ eA V)) ⟩
    castᶜ eOut ((castᶜ eIn (absurd (env-Vˢ γ Δ₁ (castᵛ eA V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-absurd eIn) ⟩
    castᶜ eOut ((absurd (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-absurd eOut ⟩
    absurd (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v))
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-absurd (eternalˡ Δ₀ lf η γ) Δ V =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (absurd (V))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-absurd e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (absurd (castᵛ e V)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-absurd lf η (castᵛ e V)) ⟩
    env-Cˢ γ Δ (absurd (env-eternal-V lf η (castᵛ e V)))
  ≡⟨ env-Cˢ-absurd γ Δ (env-eternal-V lf η (castᵛ e V)) ⟩
    absurd (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Cˢ-coerce : ∀ {St Γ A ε ε'} → (γ : Env St Γ) → (Δ : Ctx) → {p : ε ≾ₑ ε'}
              → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ‼ ε)
              → env-Cˢ γ Δ (coerce p M) ≡ coerce p (env-Cˢ γ Δ M)

env-Cˢ-coerce ⌊ St ⌋ Δ M = refl
env-Cˢ-coerce (∅ᵉ St) Δ M = refl
env-Cˢ-coerce (sliceᵉ γ q) Δ M = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-coerce γ Δ M)

env-Cˢ-coerce (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (coerce _ (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-coerce ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (coerce _ (castᶜ ei M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-coerce γ Δ' (castᶜ ei M)) ⟩
      castᶜ eo (coerce _ (env-Cˢ γ Δ' (castᶜ ei M)))
    ≡⟨ cast-coerce eo ⟩
      coerce _ (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Cˢ-coerce (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (coerce _ (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-coerce ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (coerce _ (castᶜ ei M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-coerce γ Δ' (castᶜ ei M)) ⟩
    castᶜ eo (coerce _ (env-Cˢ γ Δ' (castᶜ ei M)))
  ≡⟨ cast-coerce eo ⟩
    coerce _ (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Cˢ-coerce (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (coerce _ (M))))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-coerce eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (coerce _ (castᶜ eA M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c)) (env-Cˢ-coerce γ Δ₁ (castᶜ eA M)) ⟩
    castᶜ eOut ((castᶜ eIn (coerce _ (env-Cˢ γ Δ₁ (castᶜ eA M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-coerce eIn) ⟩
    castᶜ eOut ((coerce _ (castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-coerce eOut ⟩
    coerce _ (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Cˢ-coerce (eternalˡ Δ₀ lf η γ) Δ M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (coerce _ (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-coerce e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (coerce _ (castᶜ e M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-coerce lf η (castᶜ e M)) ⟩
    env-Cˢ γ Δ (coerce _ (env-eternal-C lf η (castᶜ e M)))
  ≡⟨ env-Cˢ-coerce γ Δ (env-eternal-C lf η (castᶜ e M)) ⟩
    coerce _ (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Vˢ-pair : ∀ {St Γ A B} → (γ : Env St Γ) → (Δ : Ctx)
            → (V : (Γ ++ᶜ Δ) ⊢V⦂ A) → (U : (Γ ++ᶜ Δ) ⊢V⦂ B)
            → env-Vˢ γ Δ ⦉ V , U ⦊ ≡ ⦉ env-Vˢ γ Δ V , env-Vˢ γ Δ U ⦊

env-Vˢ-pair ⌊ St ⌋ Δ V U = refl
env-Vˢ-pair (∅ᵉ St) Δ V U = refl
env-Vˢ-pair (sliceᵉ γ q) Δ V U = cong (V-rename (cong-ren (slice-renᵘ q))) (env-Vˢ-pair γ Δ V U)

env-Vˢ-pair (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V U =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (⦉ V , U ⦊)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-pair ei) ⟩
      castᵛ eo (env-Vˢ γ Δ' (⦉ castᵛ ei V , castᵛ ei U ⦊))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-pair γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
      castᵛ eo (⦉ env-Vˢ γ Δ' (castᵛ ei V) , env-Vˢ γ Δ' (castᵛ ei U) ⦊)
    ≡⟨ cast-pair eo ⟩
      ⦉ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) , castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U)) ⦊
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-pair (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V U =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (⦉ V , U ⦊)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-pair ei) ⟩
    castᵛ eo (env-Vˢ γ Δ' (⦉ castᵛ ei V , castᵛ ei U ⦊))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-pair γ Δ' (castᵛ ei V) (castᵛ ei U)) ⟩
    castᵛ eo (⦉ env-Vˢ γ Δ' (castᵛ ei V) , env-Vˢ γ Δ' (castᵛ ei U) ⦊)
  ≡⟨ cast-pair eo ⟩
    ⦉ castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V)) , castᵛ eo (env-Vˢ γ Δ' (castᵛ ei U)) ⦊
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-pair (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V U =
  begin
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (⦉ V , U ⦊)))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ z)) [ x ↦ Ŵ ]v))
          (cast-pair eA) ⟩
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (⦉ castᵛ eA V , castᵛ eA U ⦊))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn z) [ x ↦ Ŵ ]v)) (env-Vˢ-pair γ Δ₁ (castᵛ eA V) (castᵛ eA U)) ⟩
    castᵛ eOut ((castᵛ eIn (⦉ env-Vˢ γ Δ₁ (castᵛ eA V) , env-Vˢ γ Δ₁ (castᵛ eA U) ⦊)) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut (z [ x ↦ Ŵ ]v)) (cast-pair eIn) ⟩
    castᵛ eOut ((⦉ castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V)) , castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U)) ⦊) [ x ↦ Ŵ ]v)
  ≡⟨ cast-pair eOut ⟩
    ⦉ castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v) , castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA U))) [ x ↦ Ŵ ]v) ⦊
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Vˢ-pair (eternalˡ Δ₀ lf η γ) Δ V U =
  begin
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e (⦉ V , U ⦊)))
  ≡⟨ cong (λ z → env-Vˢ γ Δ (env-eternal-V lf η z)) (cast-pair e) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (⦉ castᵛ e V , castᵛ e U ⦊))
  ≡⟨ cong (env-Vˢ γ Δ) (env-eternal-pair lf η (castᵛ e V) (castᵛ e U)) ⟩
    env-Vˢ γ Δ (⦉ env-eternal-V lf η (castᵛ e V) , env-eternal-V lf η (castᵛ e U) ⦊)
  ≡⟨ env-Vˢ-pair γ Δ (env-eternal-V lf η (castᵛ e V)) (env-eternal-V lf η (castᵛ e U)) ⟩
    ⦉ env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V)) , env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e U)) ⦊
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Vˢ-const : ∀ {St Γ b} → (γ : Env St Γ) → (Δ : Ctx) → (c : BaseConstants b)
             → env-Vˢ γ Δ (const c) ≡ const c

env-Vˢ-const ⌊ St ⌋ Δ c = refl
env-Vˢ-const (∅ᵉ St) Δ c = refl
env-Vˢ-const (sliceᵉ γ q) Δ c = cong (V-rename (cong-ren (slice-renᵘ q))) (env-Vˢ-const γ Δ c)

env-Vˢ-const (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ c =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (const c)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-const ei) ⟩
      castᵛ eo (env-Vˢ γ Δ' (const c))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-const γ Δ' c) ⟩
      castᵛ eo (const c)
    ≡⟨ cast-const eo ⟩
      const c
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-const (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ c =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (const c)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-const ei) ⟩
    castᵛ eo (env-Vˢ γ Δ' (const c))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-const γ Δ' c) ⟩
    castᵛ eo (const c)
  ≡⟨ cast-const eo ⟩
    const c
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-const (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ c =
  begin
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (const c)))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ z)) [ x ↦ Ŵ ]v))
          (cast-const eA) ⟩
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (const c))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn z) [ x ↦ Ŵ ]v)) (env-Vˢ-const γ Δ₁ c) ⟩
    castᵛ eOut ((castᵛ eIn (const c)) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut (z [ x ↦ Ŵ ]v)) (cast-const eIn) ⟩
    castᵛ eOut ((const c) [ x ↦ Ŵ ]v)
  ≡⟨ cast-const eOut ⟩
    const c
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Vˢ-const (eternalˡ Δ₀ lf η γ) Δ c =
  begin
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e (const c)))
  ≡⟨ cong (λ z → env-Vˢ γ Δ (env-eternal-V lf η z)) (cast-const e) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (const c))
  ≡⟨ cong (env-Vˢ γ Δ) (env-eternal-const lf η c) ⟩
    env-Vˢ γ Δ (const c)
  ≡⟨ env-Vˢ-const γ Δ c ⟩
    const c
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ

env-Vˢ-⋆ : ∀ {St Γ} → (γ : Env St Γ) → (Δ : Ctx) → env-Vˢ γ Δ ⋆ ≡ ⋆

env-Vˢ-⋆ ⌊ St ⌋ Δ  = refl
env-Vˢ-⋆ (∅ᵉ St) Δ = refl
env-Vˢ-⋆ (sliceᵉ γ q) Δ = cong (V-rename (cong-ren (slice-renᵘ q))) (env-Vˢ-⋆ γ Δ)

env-Vˢ-⋆ (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ  =
  cong (V-rename (cong-ren (unbox-ren q)))
    (begin
      castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (⋆)))
    ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-⋆ ei) ⟩
      castᵛ eo (env-Vˢ γ Δ' (⋆))
    ≡⟨ cong (castᵛ eo) (env-Vˢ-⋆ γ Δ') ⟩
      castᵛ eo (⋆)
    ≡⟨ cast-⋆ eo ⟩
      ⋆
     ∎)
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ

env-Vˢ-⋆ (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ =
  begin
    castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (⋆)))
  ≡⟨ cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) (cast-⋆ ei) ⟩
    castᵛ eo (env-Vˢ γ Δ' (⋆))
  ≡⟨ cong (castᵛ eo) (env-Vˢ-⋆ γ Δ') ⟩
    castᵛ eo (⋆)
  ≡⟨ cast-⋆ eo ⟩
    ⋆
   ∎
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

env-Vˢ-⋆ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ  =
  begin
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA (⋆)))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ z)) [ x ↦ Ŵ ]v))
          (cast-⋆ eA) ⟩
    castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (⋆))) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut ((castᵛ eIn z) [ x ↦ Ŵ ]v)) (env-Vˢ-⋆ γ Δ₁) ⟩
    castᵛ eOut ((castᵛ eIn (⋆)) [ x ↦ Ŵ ]v)
  ≡⟨ cong (λ z → castᵛ eOut (z [ x ↦ Ŵ ]v)) (cast-⋆ eIn) ⟩
    castᵛ eOut ((⋆) [ x ↦ Ŵ ]v)
  ≡⟨ cast-⋆ eOut ⟩
    ⋆
  ∎
  where
    Δ₁   = [] ∷ A₀ ++ᶜ Δ
    t    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x    = split→∈ t
    Ŵ    = castᵛ (sym (split→∈-split-l t)) W
    eOut = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    eIn  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA   = ++ᶜ-assoc Γ ([] ∷ A₀) Δ

env-Vˢ-⋆ (eternalˡ Δ₀ lf η γ) Δ  =
  begin
    env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e (⋆)))
  ≡⟨ cong (λ z → env-Vˢ γ Δ (env-eternal-V lf η z)) (cast-⋆ e) ⟩
    env-Vˢ γ Δ (env-eternal-V lf η (⋆))
  ≡⟨ cong (env-Vˢ γ Δ) (env-eternal-⋆ lf η) ⟩
    env-Vˢ γ Δ (⋆)
  ≡⟨ env-Vˢ-⋆ γ Δ ⟩
    ⋆
  ∎
  where
    e = ++ᶜ-assoc Δ₀ _ Δ
-- THE ACTION COMMUTES WITH THE BINDING FORMERS
--
-- The body sits at an extended suffix, so the two sides carry casts along
-- different (but equal) proofs, reconciled by `castᶜ-irr`.

env-eternal-delay : ∀ {Δ Γ A ε τ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                  → (M : (Δ ++ᶜ Γ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
                  → env-eternal-C lf η (delay τ M)
                  ≡ delay τ (env-eternal-C lf η M)
env-eternal-delay {τ = τ} lf-[] η M =
  trans (cast-delay ++ᶜ-identityˡ)
        (cong (delay τ)
          (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))
env-eternal-delay {Δ ∷ B} {Γ} {τ = τ} (lf-∷ lf) η M =
  trans (cong (env-eternal-C lf η') (cast-delay e))
        (trans (env-eternal-delay lf η' (castᶜ (exτ e) body))
               (cong (λ z → delay τ (env-eternal-C lf η' z))
                     (castᶜ-irr (exτ e) e₂ body)))
  where
    η'   = λ {A' ρ'} (v : A' ∈[ ρ' ] Δ) → η (Tl-∷ v)
    s    = split-≡-++ᶜ {Δ ∷ B} {Γ}
    s₂   = split-≡-++ᶜ {Δ ∷ B} {Γ ⟨ of-natʳ τ ⟩}
    y    = split→∈ s
    Ŵ    = castᵛ (sym (split→∈-split-l s)) (V-rename (empty-ren lf) (η Hd))
    body = M [ Tl-⟨⟩ y ↦ Ŵ ]c
    e    = cong₂ _++ᶜ_ (split→∈-split-l s)  (split→∈-split-r s)
    e₂   = cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂)
    exτ  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ of-natʳ τ ⟩) p

env-Cˢ-delay : ∀ {St Γ A ε τ} → (γ : Env St Γ) → (Δ : Ctx)
             → (M : (Γ ++ᶜ Δ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
             → env-Cˢ γ Δ (delay τ M) ≡ delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩) M)

env-Cˢ-delay ⌊ St ⌋ Δ M = refl
env-Cˢ-delay (∅ᵉ St) Δ M = refl
env-Cˢ-delay (sliceᵉ γ q) Δ M = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-delay γ Δ M)

env-Cˢ-delay {τ = τ} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ'} γ q) Δ M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (delay τ M)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-delay ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-delay γ Δ' (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)) ⟩
      castᶜ eo (delay τ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩)
                          (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cast-delay eo ⟩
      delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) eo)
                (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cong (delay τ) (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) eo) eo₂ _) ⟩
      delay τ (castᶜ eo₂
                (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
    ≡⟨ cong (λ z → delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) z)))
            (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) ei) ei₂ M) ⟩
      delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ' ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ⟨ of-natʳ τ ⟩))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ⟨ of-natʳ τ ⟩)

env-Cˢ-delay {τ = τ} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ'} V₀ γ) Δ M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (delay τ M)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-delay ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-delay γ Δ' (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)) ⟩
    castᶜ eo (delay τ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩)
                        (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cast-delay eo ⟩
    delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) eo)
              (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cong (delay τ) (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) eo) eo₂ _) ⟩
    delay τ (castᶜ eo₂
              (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ (cong (_⟨ of-natʳ τ ⟩) ei) M)))
  ≡⟨ cong (λ z → delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) z)))
          (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) ei) ei₂ M) ⟩
    delay τ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ of-natʳ τ ⟩) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ' ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ of-natʳ τ ⟩))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ of-natʳ τ ⟩)

env-Cˢ-delay {τ = τ} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (delay τ M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-delay eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (delay τ (castᶜ (exτ eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
          (env-Cˢ-delay γ Δ₁ (castᶜ (exτ eA) M)) ⟩
    castᶜ eOut ((castᶜ eIn (delay τ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                                      (castᶜ (exτ eA) M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-delay eIn) ⟩
    castᶜ eOut ((delay τ (castᶜ (exτ eIn) (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                                            (castᶜ (exτ eA) M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-delay eOut ⟩
    delay τ (castᶜ (exτ eOut) ((castᶜ (exτ eIn) (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                                (castᶜ (exτ eA) M))) [ Tl-⟨⟩ x ↦ Ŵ ]c))
  ≡⟨ cong (delay τ) (castᶜ-irr (exτ eOut) eOut₂ _) ⟩
    delay τ (castᶜ eOut₂ ((castᶜ (exτ eIn) (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                            (castᶜ (exτ eA) M))) [ Tl-⟨⟩ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → delay τ (castᶜ eOut₂ (z [ Tl-⟨⟩ x ↦ Ŵ ]c)))
          (castᶜ-irr (exτ eIn) eIn₂ _) ⟩
    delay τ (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                            (castᶜ (exτ eA) M))) [ Tl-⟨⟩ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → delay τ (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩) z))
                            [ Tl-⟨⟩ x ↦ Ŵ ]c)))
          (castᶜ-irr (exτ eA) eA₂ M) ⟩
    delay τ (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ of-natʳ τ ⟩)
                            (castᶜ eA₂ M))) [ Tl-⟨⟩ x ↦ Ŵ ]c))
  ∎
  where
    exτ   = λ {Γ₁ Γ₂ : Ctx} (e : Γ₁ ≡ Γ₂) → cong (_⟨ of-natʳ τ ⟩) e
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    t     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t₂    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ⟨ of-natʳ τ ⟩}
    x     = split→∈ t
    Ŵ     = castᵛ (sym (split→∈-split-l t)) W
    eOut  = cong₂ _++ᶜ_ (split→∈-split-l t)  (split→∈-split-r t)
    eOut₂ = cong₂ _++ᶜ_ (split→∈-split-l t₂) (split→∈-split-r t₂)
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ of-natʳ τ ⟩))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ of-natʳ τ ⟩)

env-Cˢ-delay {τ = τ} (eternalˡ Δ₀ lf η γ) Δ M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (delay τ M)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-delay e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)))
  ≡⟨ cong (env-Cˢ γ Δ)
          (env-eternal-delay lf η (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)) ⟩
    env-Cˢ γ Δ (delay τ (env-eternal-C lf η
                          (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)))
  ≡⟨ env-Cˢ-delay γ Δ (env-eternal-C lf η (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)) ⟩
    delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩)
              (env-eternal-C lf η (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)))
  ≡⟨ cong (λ z → delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩) (env-eternal-C lf η z)))
          (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) e) e₂ M) ⟩
    delay τ (env-Cˢ γ (Δ ⟨ of-natʳ τ ⟩) (env-eternal-C lf η (castᶜ e₂ M)))
  ∎
  where
    e  = ++ᶜ-assoc Δ₀ _ Δ
    e₂ = ++ᶜ-assoc Δ₀ _ (Δ ⟨ of-natʳ τ ⟩)

env-eternal-seq : ∀ {Δ Γ A B ε ε'} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (M : (Δ ++ᶜ Γ) ⊢C⦂ A ‼ ε)
                → (N : (Δ ++ᶜ Γ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
                → env-eternal-C lf η (M ⨟ N)
                ≡ (env-eternal-C lf η M) ⨟ (env-eternal-C lf η N)

env-eternal-seq {A = A} {ε = ε} lf-[] η M N =
  trans (cast-seq ++ᶜ-identityˡ)
        (cong ((castᶜ ++ᶜ-identityˡ M) ⨟_)
          (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) ++ᶜ-identityˡ)
                     ++ᶜ-identityˡ N))

env-eternal-seq {Δ ∷ B₀} {Γ} {A} {ε = ε} (lf-∷ lf) η M N =
  trans (cong (env-eternal-C lf η') (cast-seq e))
        (trans (env-eternal-seq lf η' (castᶜ e bodyM) (castᶜ (exε e) bodyN))
               (cong (λ z → (env-eternal-C lf η' (castᶜ e bodyM))
                              ⨟ (env-eternal-C lf η' z))
                     (castᶜ-irr (exε e) e₂ bodyN)))
  where
    η'    = λ {A' ρ'} (v : A' ∈[ ρ' ] Δ) → η (Tl-∷ v)
    s     = split-≡-++ᶜ {Δ ∷ B₀} {Γ}
    s₂    = split-≡-++ᶜ {Δ ∷ B₀} {Γ ⟨ mapᵉ ε ⟩ ∷ A}
    y     = split→∈ s
    Ŵ     = castᵛ (sym (split→∈-split-l s)) (V-rename (empty-ren lf) (η Hd))
    bodyM = M [ y ↦ Ŵ ]c
    bodyN = N [ Tl-∷ (Tl-⟨⟩ y) ↦ Ŵ ]c
    e     = cong₂ _++ᶜ_ (split→∈-split-l s)  (split→∈-split-r s)
    e₂    = cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂)
    exε   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
           → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ‼ ε)
           → (N : (Γ ++ᶜ Δ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
           → env-Cˢ γ Δ (M ⨟ N)
           ≡ (env-Cˢ γ Δ M) ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) N)

env-Cˢ-seq ⌊ St ⌋ Δ M N = refl
env-Cˢ-seq (∅ᵉ St) Δ M N = refl
env-Cˢ-seq (sliceᵉ γ q) Δ M N = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-seq γ Δ M N)

env-Cˢ-seq {A = A} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (M ⨟ N)))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-seq ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' ((castᶜ ei M) ⨟ (castᶜ (exε ei) N)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-seq γ Δ' (castᶜ ei M) (castᶜ (exε ei) N)) ⟩
      castᶜ eo ((env-Cˢ γ Δ' (castᶜ ei M))
                  ⨟ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cast-seq eo ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ (exε eo) (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cong ((castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) ⨟_)
            (castᶜ-irr (exε eo) eo₂ _) ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
    ≡⟨ cong (λ z → (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
                     ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) z)))
            (castᶜ-irr (exε ei) ei₂ N) ⟩
      (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
        ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ ei₂ N)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ M N =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (M ⨟ N)))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-seq ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' ((castᶜ ei M) ⨟ (castᶜ (exε ei) N)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-seq γ Δ' (castᶜ ei M) (castᶜ (exε ei) N)) ⟩
    castᶜ eo ((env-Cˢ γ Δ' (castᶜ ei M))
                ⨟ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cast-seq eo ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ (exε eo) (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cong ((castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M))) ⨟_)
          (castᶜ-irr (exε eo) eo₂ _) ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε ei) N)))
  ≡⟨ cong (λ z → (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
                   ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) z)))
          (castᶜ-irr (exε ei) ei₂ N) ⟩
    (castᶜ eo (env-Cˢ γ Δ' (castᶜ ei M)))
      ⨟ (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ ei₂ N)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M N =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (M ⨟ N)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-seq eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ ((castᶜ eA M) ⨟ (castᶜ (exε eA) N))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
          (env-Cˢ-seq γ Δ₁ (castᶜ eA M) (castᶜ (exε eA) N)) ⟩
    castᶜ eOut ((castᶜ eIn ((env-Cˢ γ Δ₁ (castᶜ eA M))
                             ⨟ (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε eA) N))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-seq eIn) ⟩
    castᶜ eOut (((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M)))
                  ⨟ (castᶜ (exε eIn) (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castᶜ (exε eA) N)))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-seq eOut ⟩
    (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
      ⨟ (castᶜ (exε eOut) ((castᶜ (exε eIn)
            (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε eA) N)))
              [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ≡⟨ cong ((castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c)) ⨟_)
          (castᶜ-irr (exε eOut) eOut₂ _) ⟩
    (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
      ⨟ (castᶜ eOut₂ ((castᶜ (exε eIn)
            (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε eA) N)))
              [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
                   ⨟ (castᶜ eOut₂ (z [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c)))
          (castᶜ-irr (exε eIn) eIn₂ _) ⟩
    (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
      ⨟ (castᶜ eOut₂ ((castᶜ eIn₂
            (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ (exε eA) N)))
              [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
                   ⨟ (castᶜ eOut₂ ((castᶜ eIn₂
                        (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) z))
                          [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c)))
          (castᶜ-irr (exε eA) eA₂ N) ⟩
    (castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA M))) [ x ↦ Ŵ ]c))
      ⨟ (castᶜ eOut₂ ((castᶜ eIn₂
            (env-Cˢ γ (Δ₁ ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ eA₂ N)))
              [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    t     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t₂    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ⟨ mapᵉ ε ⟩ ∷ A}
    x     = split→∈ t
    Ŵ     = castᵛ (sym (split→∈-split-l t)) W
    eOut  = cong₂ _++ᶜ_ (split→∈-split-l t)  (split→∈-split-r t)
    eOut₂ = cong₂ _++ᶜ_ (split→∈-split-l t₂) (split→∈-split-r t₂)
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-Cˢ-seq {A = A} {ε = ε} (eternalˡ Δ₀ lf η γ) Δ M N =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (M ⨟ N)))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-seq e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η ((castᶜ e M) ⨟ (castᶜ (exε e) N)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-seq lf η (castᶜ e M) (castᶜ (exε e) N)) ⟩
    env-Cˢ γ Δ ((env-eternal-C lf η (castᶜ e M))
                  ⨟ (env-eternal-C lf η (castᶜ (exε e) N)))
  ≡⟨ env-Cˢ-seq γ Δ (env-eternal-C lf η (castᶜ e M))
                    (env-eternal-C lf η (castᶜ (exε e) N)) ⟩
    (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
      ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) (env-eternal-C lf η (castᶜ (exε e) N)))
  ≡⟨ cong (λ z → (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
                   ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) (env-eternal-C lf η z)))
          (castᶜ-irr (exε e) e₂ N) ⟩
    (env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e M)))
      ⨟ (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) (env-eternal-C lf η (castᶜ e₂ N)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    e₂  = ++ᶜ-assoc Δ₀ _ (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    exε = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) p

env-eternal-perform : ∀ {Δ Γ A ε} {op : Op} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ type-of-gtype (param op))
                → (M : (Δ ++ᶜ Γ) ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
                → env-eternal-C lf η (perform op (V) (M))
                ≡ perform op (env-eternal-V lf η V) (env-eternal-C lf η M)

env-eternal-perform {op = op} lf-[] η V M =
  trans (cast-perform ++ᶜ-identityˡ)
        (cong (λ z → perform op (castᵛ ++ᶜ-identityˡ V) (z))
          (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))

env-eternal-perform {Δ ∷ B₀} {Γ} {op = op} (lf-∷ lf) η V M =
  trans (cong (env-eternal-C lf η') (cast-perform e))
        (trans (env-eternal-perform lf η' (castᵛ e bodyV) (castᶜ (exf e) bodyM))
               (cong (λ z → perform op (env-eternal-V lf η' (castᵛ e bodyV)) (env-eternal-C lf η' z))
                     (castᶜ-irr (exf e) e₂ bodyM)))
  where
    η'    = λ {A' ρ'} (v : A' ∈[ ρ' ] Δ) → η (Tl-∷ v)
    s     = split-≡-++ᶜ {Δ ∷ B₀} {Γ}
    s₂    = split-≡-++ᶜ {Δ ∷ B₀} {Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)}
    y     = split→∈ s
    Ŵ     = castᵛ (sym (split→∈-split-l s)) (V-rename (empty-ren lf) (η Hd))
    bodyV = V [ y ↦ Ŵ ]v
    bodyM = M [ Tl-∷ (Tl-⟨⟩ y) ↦ Ŵ ]c
    e     = cong₂ _++ᶜ_ (split→∈-split-l s)  (split→∈-split-r s)
    e₂    = cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂)
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform : ∀ {St Γ A ε} {op : Op} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ type-of-gtype (param op))
           → (M : (Γ ++ᶜ Δ) ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
           → env-Cˢ γ Δ (perform op (V) (M))
           ≡ perform op (env-Vˢ γ Δ V) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) M)

env-Cˢ-perform ⌊ St ⌋ Δ V M = refl
env-Cˢ-perform (∅ᵉ St) Δ V M = refl
env-Cˢ-perform (sliceᵉ γ q) Δ V M = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-perform γ Δ V M)

env-Cˢ-perform {op = op} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (perform op (V) (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-perform ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (perform op (castᵛ ei V) (castᶜ (exf ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-perform γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
      castᶜ eo (perform op (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
    ≡⟨ cast-perform eo ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ (exf eo) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (z))
            (castᶜ-irr (exf eo) eo₂ _) ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) z)))
            (castᶜ-irr (exf ei) ei₂ M) ⟩
      perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform {op = op} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (perform op (V) (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-perform ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (perform op (castᵛ ei V) (castᶜ (exf ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-perform γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
    castᶜ eo (perform op (env-Vˢ γ Δ' (castᵛ ei V)) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
  ≡⟨ cast-perform eo ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ (exf eo) (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (z))
          (castᶜ-irr (exf eo) eo₂ _) ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) z)))
          (castᶜ-irr (exf ei) ei₂ M) ⟩
    perform op (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) (castᶜ eo₂ (env-Cˢ γ (Δ' ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform {op = op} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (perform op (V) (M))))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-perform eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (perform op (castᵛ eA V) (castᶜ (exf eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
          (env-Cˢ-perform γ Δ₁ (castᵛ eA V) (castᶜ (exf eA) M)) ⟩
    castᶜ eOut ((castᶜ eIn (perform op (env-Vˢ γ Δ₁ (castᵛ eA V)) (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-perform eIn) ⟩
    castᶜ eOut ((perform op (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) (castᶜ (exf eIn) (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cast-perform eOut ⟩
    perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (castᶜ (exf eOut) ((castᶜ (exf eIn) (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf eA) M))) [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (z))
          (castᶜ-irr (exf eOut) eOut₂ _) ⟩
    perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (castᶜ eOut₂ ((castᶜ (exf eIn) (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf eA) M))) [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (castᶜ eOut₂ (z [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c)))
          (castᶜ-irr (exf eIn) eIn₂ _) ⟩
    perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ (exf eA) M))) [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) z)) [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c)))
          (castᶜ-irr (exf eA) eA₂ M) ⟩
    perform op (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (castᶜ eA₂ M))) [ Tl-∷ (Tl-⟨⟩ x) ↦ Ŵ ]c))
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    t     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t₂    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)}
    x     = split→∈ t
    Ŵ     = castᵛ (sym (split→∈-split-l t)) W
    eOut  = cong₂ _++ᶜ_ (split→∈-split-l t)  (split→∈-split-r t)
    eOut₂ = cong₂ _++ᶜ_ (split→∈-split-l t₂) (split→∈-split-r t₂)
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-Cˢ-perform {op = op} (eternalˡ Δ₀ lf η γ) Δ V M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (perform op (V) (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-perform e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (perform op (castᵛ e V) (castᶜ (exf e) M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-perform lf η (castᵛ e V) (castᶜ (exf e) M)) ⟩
    env-Cˢ γ Δ (perform op (env-eternal-V lf η (castᵛ e V)) (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ env-Cˢ-perform γ Δ (env-eternal-V lf η (castᵛ e V))
                    (env-eternal-C lf η (castᶜ (exf e) M)) ⟩
    perform op (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ cong (λ z → perform op (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (env-eternal-C lf η z)))
          (castᶜ-irr (exf e) e₂ M) ⟩
    perform op (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) (env-Cˢ γ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) (env-eternal-C lf η (castᶜ e₂ M)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    e₂  = ++ᶜ-assoc Δ₀ _ (Δ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op))
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)) p

env-eternal-match : ∀ {Δ Γ A B C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⊢V⦂ A |×| B)
                → (M : (Δ ++ᶜ Γ) ∷ A ∷ B ⊢C⦂ C)
                → env-eternal-C lf η (match (V) `in (M))
                ≡ match (env-eternal-V lf η V) `in (env-eternal-C lf η M)

env-eternal-match {A = A} {B = B} lf-[] η V M =
  trans (cast-match ++ᶜ-identityˡ)
        (cong (λ z → match (castᵛ ++ᶜ-identityˡ V) `in (z))
          (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) ++ᶜ-identityˡ) ++ᶜ-identityˡ M))

env-eternal-match {Δ ∷ B₀} {Γ} {A = A} {B = B} (lf-∷ lf) η V M =
  trans (cong (env-eternal-C lf η') (cast-match e))
        (trans (env-eternal-match lf η' (castᵛ e bodyV) (castᶜ (exf e) bodyM))
               (cong (λ z → match (env-eternal-V lf η' (castᵛ e bodyV)) `in (env-eternal-C lf η' z))
                     (castᶜ-irr (exf e) e₂ bodyM)))
  where
    η'    = λ {A' ρ'} (v : A' ∈[ ρ' ] Δ) → η (Tl-∷ v)
    s     = split-≡-++ᶜ {Δ ∷ B₀} {Γ}
    s₂    = split-≡-++ᶜ {Δ ∷ B₀} {Γ ∷ A ∷ B}
    y     = split→∈ s
    Ŵ     = castᵛ (sym (split→∈-split-l s)) (V-rename (empty-ren lf) (η Hd))
    bodyV = V [ y ↦ Ŵ ]v
    bodyM = M [ Tl-∷ (Tl-∷ y) ↦ Ŵ ]c
    e     = cong₂ _++ᶜ_ (split→∈-split-l s)  (split→∈-split-r s)
    e₂    = cong₂ _++ᶜ_ (split→∈-split-l s₂) (split→∈-split-r s₂)
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match : ∀ {St Γ A B C} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⊢V⦂ A |×| B)
           → (M : (Γ ++ᶜ Δ) ∷ A ∷ B ⊢C⦂ C)
           → env-Cˢ γ Δ (match (V) `in (M))
           ≡ match (env-Vˢ γ Δ V) `in (env-Cˢ γ (Δ ∷ A ∷ B) M)

env-Cˢ-match ⌊ St ⌋ Δ V M = refl
env-Cˢ-match (∅ᵉ St) Δ V M = refl
env-Cˢ-match (sliceᵉ γ q) Δ V M = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-match γ Δ V M)

env-Cˢ-match {A = A} {B = B} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (match (V) `in (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-match ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (match (castᵛ ei V) `in (castᶜ (exf ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-match γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
      castᶜ eo (match (env-Vˢ γ Δ' (castᵛ ei V)) `in (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
    ≡⟨ cast-match eo ⟩
      match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ (exf eo) (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (z))
            (castᶜ-irr (exf eo) eo₂ _) ⟩
      match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
    ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) z)))
            (castᶜ-irr (exf ei) ei₂ M) ⟩
      match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ ei₂ M)))
     ∎)
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ∷ A ∷ B))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ∷ A ∷ B)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match {A = A} {B = B} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (match (V) `in (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-match ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (match (castᵛ ei V) `in (castᶜ (exf ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-match γ Δ' (castᵛ ei V) (castᶜ (exf ei) M)) ⟩
    castᶜ eo (match (env-Vˢ γ Δ' (castᵛ ei V)) `in (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
  ≡⟨ cast-match eo ⟩
    match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ (exf eo) (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (z))
          (castᶜ-irr (exf eo) eo₂ _) ⟩
    match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ (exf ei) M)))
  ≡⟨ cong (λ z → match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) z)))
          (castᶜ-irr (exf ei) ei₂ M) ⟩
    match (castᵛ eo (env-Vˢ γ Δ' (castᵛ ei V))) `in (castᶜ eo₂ (env-Cˢ γ (Δ' ∷ A ∷ B) (castᶜ ei₂ M)))
   ∎
  where
    Δ₁  = [] ∷ [ ρ ] A₀
    Δ'  = Δ₁ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei  = ++ᶜ-assoc Γ Δ₁ Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ A ∷ B))
    ei₂ = ++ᶜ-assoc Γ Δ₁ (Δ ∷ A ∷ B)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match {A = A} {B = B} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (match (V) `in (M))))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-match eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (match (castᵛ eA V) `in (castᶜ (exf eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
          (env-Cˢ-match γ Δ₁ (castᵛ eA V) (castᶜ (exf eA) M)) ⟩
    castᶜ eOut ((castᶜ eIn (match (env-Vˢ γ Δ₁ (castᵛ eA V)) `in (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-match eIn) ⟩
    castᶜ eOut ((match (castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) `in (castᶜ (exf eIn) (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M))))
                  [ x ↦ Ŵ ]c)
  ≡⟨ cast-match eOut ⟩
    match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (castᶜ (exf eOut) ((castᶜ (exf eIn) (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M))) [ Tl-∷ (Tl-∷ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (z))
          (castᶜ-irr (exf eOut) eOut₂ _) ⟩
    match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (castᶜ eOut₂ ((castᶜ (exf eIn) (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M))) [ Tl-∷ (Tl-∷ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (castᶜ eOut₂ (z [ Tl-∷ (Tl-∷ x) ↦ Ŵ ]c)))
          (castᶜ-irr (exf eIn) eIn₂ _) ⟩
    match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ (exf eA) M))) [ Tl-∷ (Tl-∷ x) ↦ Ŵ ]c))
  ≡⟨ cong (λ z → match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ∷ A ∷ B) z)) [ Tl-∷ (Tl-∷ x) ↦ Ŵ ]c)))
          (castᶜ-irr (exf eA) eA₂ M) ⟩
    match (castᵛ eOut ((castᵛ eIn (env-Vˢ γ Δ₁ (castᵛ eA V))) [ x ↦ Ŵ ]v)) `in (castᶜ eOut₂ ((castᶜ eIn₂ (env-Cˢ γ (Δ₁ ∷ A ∷ B) (castᶜ eA₂ M))) [ Tl-∷ (Tl-∷ x) ↦ Ŵ ]c))
  ∎
  where
    Δ₁    = [] ∷ A₀ ++ᶜ Δ
    t     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t₂    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ∷ A ∷ B}
    x     = split→∈ t
    Ŵ     = castᵛ (sym (split→∈-split-l t)) W
    eOut  = cong₂ _++ᶜ_ (split→∈-split-l t)  (split→∈-split-r t)
    eOut₂ = cong₂ _++ᶜ_ (split→∈-split-l t₂) (split→∈-split-r t₂)
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A ∷ B))
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ A ∷ B)
    exf   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-Cˢ-match {A = A} {B = B} (eternalˡ Δ₀ lf η γ) Δ V M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (match (V) `in (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-match e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (match (castᵛ e V) `in (castᶜ (exf e) M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-match lf η (castᵛ e V) (castᶜ (exf e) M)) ⟩
    env-Cˢ γ Δ (match (env-eternal-V lf η (castᵛ e V)) `in (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ env-Cˢ-match γ Δ (env-eternal-V lf η (castᵛ e V))
                    (env-eternal-C lf η (castᶜ (exf e) M)) ⟩
    match (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) `in (env-Cˢ γ (Δ ∷ A ∷ B) (env-eternal-C lf η (castᶜ (exf e) M)))
  ≡⟨ cong (λ z → match (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) `in (env-Cˢ γ (Δ ∷ A ∷ B) (env-eternal-C lf η z)))
          (castᶜ-irr (exf e) e₂ M) ⟩
    match (env-Vˢ γ Δ (env-eternal-V lf η (castᵛ e V))) `in (env-Cˢ γ (Δ ∷ A ∷ B) (env-eternal-C lf η (castᶜ e₂ M)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    e₂  = ++ᶜ-assoc Δ₀ _ (Δ ∷ A ∷ B)
    exf = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (λ Γ₀ → Γ₀ ∷ A ∷ B) p

env-eternal-box : ∀ {Δ Γ A C ρ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → (V : (Δ ++ᶜ Γ) ⟨ ρ ⟩ ⊢V⦂ A)
                → (M : (Δ ++ᶜ Γ) ∷ [ ρ ] A ⊢C⦂ C)
                → env-eternal-C lf η (box V M)
                ≡ box (env-eternal-V lf η V) (env-eternal-C lf η M)

env-eternal-box {A = A} {ρ = ρ} lf-[] η V M =
  trans (cast-box ++ᶜ-identityˡ)
        (trans (cong (λ z → box z (castᶜ (cong (_∷ [ ρ ] A) ++ᶜ-identityˡ) M))
                 (castᵛ-irr (cong (_⟨ ρ ⟩) ++ᶜ-identityˡ) ++ᶜ-identityˡ V))
               (cong (λ z → box (castᵛ ++ᶜ-identityˡ V) z)
                 (castᶜ-irr (cong (_∷ [ ρ ] A) ++ᶜ-identityˡ) ++ᶜ-identityˡ M)))

env-eternal-box {Δ ∷ B₀} {Γ} {A = A} {ρ = ρ} (lf-∷ lf) η V M =
  trans (cong (env-eternal-C lf η') (cast-box e))
        (trans (env-eternal-box lf η' (castᵛ (exV e) bodyV) (castᶜ (exM e) bodyM))
               (trans (cong (λ z → box (env-eternal-V lf η' z)
                                       (env-eternal-C lf η' (castᶜ (exM e) bodyM)))
                        (castᵛ-irr (exV e) eV₂ bodyV))
                      (cong (λ z → box (env-eternal-V lf η' (castᵛ eV₂ bodyV))
                                       (env-eternal-C lf η' z))
                        (castᶜ-irr (exM e) eM₂ bodyM))))
  where
    η'    = λ {A' ρ'} (v : A' ∈[ ρ' ] Δ) → η (Tl-∷ v)
    s     = split-≡-++ᶜ {Δ ∷ B₀} {Γ}
    sV    = split-≡-++ᶜ {Δ ∷ B₀} {Γ ⟨ ρ ⟩}
    sM    = split-≡-++ᶜ {Δ ∷ B₀} {Γ ∷ [ ρ ] A}
    y     = split→∈ s
    Ŵ     = castᵛ (sym (split→∈-split-l s)) (V-rename (empty-ren lf) (η Hd))
    bodyV = V [ Tl-⟨⟩ y ↦ Ŵ ]v
    bodyM = M [ Tl-∷ y ↦ Ŵ ]c
    e     = cong₂ _++ᶜ_ (split→∈-split-l s)  (split→∈-split-r s)
    eV₂   = cong₂ _++ᶜ_ (split→∈-split-l sV) (split→∈-split-r sV)
    eM₂   = cong₂ _++ᶜ_ (split→∈-split-l sM) (split→∈-split-r sM)
    exV   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM   = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box : ∀ {St Γ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
           → (V : (Γ ++ᶜ Δ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : (Γ ++ᶜ Δ) ∷ [ ρ ] A ⊢C⦂ C)
           → env-Cˢ γ Δ (box V M)
           ≡ box (env-Vˢ γ (Δ ⟨ ρ ⟩) V) (env-Cˢ γ (Δ ∷ [ ρ ] A) M)

env-Cˢ-box ⌊ St ⌋ Δ V M = refl
env-Cˢ-box (∅ᵉ St) Δ V M = refl
env-Cˢ-box (sliceᵉ γ q) Δ V M = cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-box γ Δ V M)

env-Cˢ-box {A = A} {ρ = ρ} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ'} γ q) Δ V M =
  cong (C-rename (cong-ren (unbox-ren q)))
    (begin
      castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (box (V) (M))))
    ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-box ei) ⟩
      castᶜ eo (env-Cˢ γ Δ' (box (castᵛ (exV ei) V) (castᶜ (exM ei) M)))
    ≡⟨ cong (castᶜ eo) (env-Cˢ-box γ Δ' (castᵛ (exV ei) V) (castᶜ (exM ei) M)) ⟩
      castᶜ eo (box (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V)) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cast-box eo ⟩
      box (castᵛ (exV eo) (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (z) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
            (castᵛ-irr (exV eo) eoV₂ _) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (z))
            (castᶜ-irr (exM eo) eoM₂ _) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) z)) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
            (castᵛ-irr (exV ei) eiV₂ V) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
    ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) z)))
            (castᶜ-irr (exM ei) eiM₂ M) ⟩
      box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ eiM₂ M)))
     ∎)
  where
    Δ'   = [] ⟨ ρ' ⟩ ++ᶜ Δ
    eo   = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) Δ)
    ei   = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) Δ
    eoV₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ⟨ ρ ⟩))
    eoM₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ' ⟩) (Δ ∷ [ ρ ] A))
    eiV₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ⟨ ρ ⟩)
    eiM₂ = ++ᶜ-assoc Γ ([] ⟨ ρ' ⟩) (Δ ∷ [ ρ ] A)
    exV  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box {A = A} {ρ = ρ} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ'} V₀ γ) Δ V M =
  begin
    castᶜ eo (env-Cˢ γ Δ' (castᶜ ei (box (V) (M))))
  ≡⟨ cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-box ei) ⟩
    castᶜ eo (env-Cˢ γ Δ' (box (castᵛ (exV ei) V) (castᶜ (exM ei) M)))
  ≡⟨ cong (castᶜ eo) (env-Cˢ-box γ Δ' (castᵛ (exV ei) V) (castᶜ (exM ei) M)) ⟩
    castᶜ eo (box (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V)) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cast-box eo ⟩
    box (castᵛ (exV eo) (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (z) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
          (castᵛ-irr (exV eo) eoV₂ _) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ (exM eo) (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (z))
          (castᶜ-irr (exM eo) eoM₂ _) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ (exV ei) V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) z)) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M))))
          (castᵛ-irr (exV ei) eiV₂ V) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ (exM ei) M)))
  ≡⟨ cong (λ z → box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) z)))
          (castᶜ-irr (exM ei) eiM₂ M) ⟩
    box (castᵛ eoV₂ (env-Vˢ γ (Δ' ⟨ ρ ⟩) (castᵛ eiV₂ V))) (castᶜ eoM₂ (env-Cˢ γ (Δ' ∷ [ ρ ] A) (castᶜ eiM₂ M)))
   ∎
  where
    Δ₁   = [] ∷ [ ρ' ] A₀
    Δ'   = Δ₁ ++ᶜ Δ
    eo   = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei   = ++ᶜ-assoc Γ Δ₁ Δ
    eoV₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ⟨ ρ ⟩))
    eoM₂ = sym (++ᶜ-assoc (toCtx St) Δ₁ (Δ ∷ [ ρ ] A))
    eiV₂ = ++ᶜ-assoc Γ Δ₁ (Δ ⟨ ρ ⟩)
    eiM₂ = ++ᶜ-assoc Γ Δ₁ (Δ ∷ [ ρ ] A)
    exV  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM  = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box {A = A} {ρ = ρ} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ V M =
  begin
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (castᶜ eA (box (V) (M))))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ z)) [ x ↦ Ŵ ]c))
          (cast-box eA) ⟩
    castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ₁ (box (castᵛ (exV eA) V) (castᶜ (exM eA) M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
          (env-Cˢ-box γ Δ₁ (castᵛ (exV eA) V) (castᶜ (exM eA) M)) ⟩
    castᶜ eOut ((castᶜ eIn (box (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V)) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-box eIn) ⟩
    castᶜ eOut ((box (castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) (castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M)))) [ x ↦ Ŵ ]c)
  ≡⟨ cast-box eOut ⟩
    box (castᵛ (exV eOut) ((castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ (exM eOut) ((castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → box (z) (castᶜ (exM eOut) ((castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c)))
          (castᵛ-irr (exV eOut) eOutV₂ _) ⟩
    box (castᵛ eOutV₂ ((castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ (exM eOut) ((castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → box (castᵛ eOutV₂ ((castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (z))
          (castᶜ-irr (exM eOut) eOutM₂ _) ⟩
    box (castᵛ eOutV₂ ((castᵛ (exV eIn) (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → box (castᵛ eOutV₂ (z [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c)))
          (castᵛ-irr (exV eIn) eInV₂ _) ⟩
    box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ (exM eIn) (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ (z [ Tl-∷ x ↦ Ŵ ]c)))
          (castᶜ-irr (exM eIn) eInM₂ _) ⟩
    box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ (exV eA) V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) z)) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c)))
          (castᵛ-irr (exV eA) eAV₂ V) ⟩
    box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ (exM eA) M))) [ Tl-∷ x ↦ Ŵ ]c))
  ≡⟨ cong (λ z → box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) z)) [ Tl-∷ x ↦ Ŵ ]c)))
          (castᶜ-irr (exM eA) eAM₂ M) ⟩
    box (castᵛ eOutV₂ ((castᵛ eInV₂ (env-Vˢ γ (Δ₁ ⟨ ρ ⟩) (castᵛ eAV₂ V))) [ Tl-⟨⟩ x ↦ Ŵ ]v)) (castᶜ eOutM₂ ((castᶜ eInM₂ (env-Cˢ γ (Δ₁ ∷ [ ρ ] A) (castᶜ eAM₂ M))) [ Tl-∷ x ↦ Ŵ ]c))
  ∎
  where
    Δ₁     = [] ∷ A₀ ++ᶜ Δ
    t      = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    tV     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ⟨ ρ ⟩}
    tM     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ∷ [ ρ ] A}
    x      = split→∈ t
    Ŵ      = castᵛ (sym (split→∈-split-l t)) W
    eOut   = cong₂ _++ᶜ_ (split→∈-split-l t)  (split→∈-split-r t)
    eOutV₂ = cong₂ _++ᶜ_ (split→∈-split-l tV) (split→∈-split-r tV)
    eOutM₂ = cong₂ _++ᶜ_ (split→∈-split-l tM) (split→∈-split-r tM)
    eIn    = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eInV₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ ρ ⟩))
    eInM₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ [ ρ ] A))
    eA     = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eAV₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ ρ ⟩)
    eAM₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ∷ [ ρ ] A)
    exV    = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM    = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

env-Cˢ-box {A = A} {ρ = ρ} (eternalˡ Δ₀ lf η γ) Δ V M =
  begin
    env-Cˢ γ Δ (env-eternal-C lf η (castᶜ e (box (V) (M))))
  ≡⟨ cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-box e) ⟩
    env-Cˢ γ Δ (env-eternal-C lf η (box (castᵛ (exV e) V) (castᶜ (exM e) M)))
  ≡⟨ cong (env-Cˢ γ Δ) (env-eternal-box lf η (castᵛ (exV e) V) (castᶜ (exM e) M)) ⟩
    env-Cˢ γ Δ (box (env-eternal-V lf η (castᵛ (exV e) V)) (env-eternal-C lf η (castᶜ (exM e) M)))
  ≡⟨ env-Cˢ-box γ Δ (env-eternal-V lf η (castᵛ (exV e) V)) (env-eternal-C lf η (castᶜ (exM e) M)) ⟩
    box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ (exV e) V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ (exM e) M)))
  ≡⟨ cong (λ z → box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η z)) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ (exM e) M))))
          (castᵛ-irr (exV e) eV₂ V) ⟩
    box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ eV₂ V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ (exM e) M)))
  ≡⟨ cong (λ z → box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ eV₂ V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η z)))
          (castᶜ-irr (exM e) eM₂ M) ⟩
    box (env-Vˢ γ (Δ ⟨ ρ ⟩) (env-eternal-V lf η (castᵛ eV₂ V))) (env-Cˢ γ (Δ ∷ [ ρ ] A) (env-eternal-C lf η (castᶜ eM₂ M)))
  ∎
  where
    e   = ++ᶜ-assoc Δ₀ _ Δ
    eV₂ = ++ᶜ-assoc Δ₀ _ (Δ ⟨ ρ ⟩)
    eM₂ = ++ᶜ-assoc Δ₀ _ (Δ ∷ [ ρ ] A)
    exV = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_⟨ ρ ⟩) p
    exM = λ {Γ₁ Γ₂ : Ctx} (p : Γ₁ ≡ Γ₂) → cong (_∷ [ ρ ] A) p

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

-- The action commutes with substituting a telescope entry, definitionally:
-- at the empty suffix every cast is `refl` (`++ᶜ-assoc Γ Γ' []` is, and so is
-- `cong₂ _++ᶜ_ refl refl`) and the variable is `Hd`.

env-Cˢ-head : ∀ {St Γ A C} → (γ : Env St Γ) → (M : Γ ∷ A ⊢C⦂ C)
            → (W : toCtx St ⊢V⦂ A)
            → (env-Cˢ γ ([] ∷ A) M) [ Hd ↦ W ]c ≡ env-C (γ ∷ᵉ W) M
env-Cˢ-head γ M W = refl

-- The same for a freshly allocated cell, and this is the point of `liftᵉ`: the
-- reduct of `BOX` already lives over the new state's context, and it *is* the
-- action there — no substitution, hence no contraction law.

env-Cˢ-lift : ∀ {St Γ A C ρ} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → (γ : Env St Γ) → (M : Γ ∷ [ ρ ] A ⊢C⦂ C)
            → env-Cˢ γ ([] ∷ [ ρ ] A) M ≡ env-C (liftᵉ V γ) M
env-Cˢ-lift V γ M = refl

env-Vˢ-lift : ∀ {St Γ A B ρ} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → (γ : Env St Γ) → (W : Γ ∷ [ ρ ] A ⊢V⦂ B)
            → env-Vˢ γ ([] ∷ [ ρ ] A) W ≡ env-V (liftᵉ V γ) W
env-Vˢ-lift V γ W = refl

-- The eternal zone's own action on a clause family: each of its substitutions
-- reaches the clauses through `⟨_⟩[_↦_]cl`, as `_∷ᵉ_`'s does.

env-eternal-H : ∀ {Δ Γ B} → (lf : Lock-free Δ) → ClosedVals Δ
              → Fam B ((Δ ++ᶜ Γ) ᴱ) → Fam B (Γ ᴱ)

env-eternal-H {Γ = Γ} {B = B} lf-[] η K op ε =
  Cl-cast op ε (++ᶜ-identityˡ {Γ}) (K op ε)

env-eternal-H {Δ ∷ B₀} {Γ} {B} (lf-∷ lf) η K =
  env-eternal-H {Δ} {Γ} {B} lf (λ x → η (Tl-∷ x))
    (λ op ε →
       Cl-cast op ε (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
         (⟨ eternal? B₀ ⟩[ split→∈ s
                          ↦ castᵛ (sym (split→∈-split-l s))
                              (V-rename (empty-ren lf) (η Hd)) ]cl K op ε))
  where
    s = split-≡-++ᶜ {Δ ∷ B₀} {Γ}

-- Hence the eternal zone commutes with `handle`: `env-eternal-C`'s two clauses
-- against `cast-handle`, whose clause transport is `Cl-cast` on the nose.

env-eternal-handle : ∀ {Δ Γ A B ε ε'} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                   → (M : (Δ ++ᶜ Γ) ⊢C⦂ A ‼ ε)
                   → (H : Fam B ((Δ ++ᶜ Γ) ᴱ))
                   → (N : (Δ ++ᶜ Γ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
                   → env-eternal-C lf η (handle M `with H `in N)
                   ≡ handle (env-eternal-C lf η M)
                      `with env-eternal-H {Δ} {Γ} {B} lf η H
                      `in (env-eternal-C {Γ = Γ ⟨ mapᵉ ε ⟩ ∷ A} lf η N)

env-eternal-handle {Γ = Γ} {A = A} {ε = ε} lf-[] η M H N =
  trans (cast-handle (++ᶜ-identityˡ {Γ}))
        (cong (λ z → handle (castᶜ ++ᶜ-identityˡ M)
                      `with env-eternal-H {[]} {Γ} lf-[] η H `in z)
              (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) (++ᶜ-identityˡ {Γ}))
                         (++ᶜ-identityˡ {Γ ⟨ mapᵉ ε ⟩ ∷ A}) N))

env-eternal-handle {Δ ∷ B₀} {Γ} {A = A} {ε = ε} (lf-∷ lf) η M H N =
  trans (cong (env-eternal-C lf η') (cast-handle e))
    (trans (cong (λ z → env-eternal-C lf η'
                          (handle (castᶜ e _) `with _ `in z))
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) e' _))
           (env-eternal-handle lf η' _ _ _))
  where
    η' = λ {A' ρ'} (x : A' ∈[ ρ' ] Δ) → η (Tl-∷ x)
    s  = split-≡-++ᶜ {Δ ∷ B₀} {Γ}
    e  = cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s)
    s' = split-≡-++ᶜ {Δ ∷ B₀} {Γ ⟨ mapᵉ ε ⟩ ∷ A}
    e' = cong₂ _++ᶜ_ (split→∈-split-l s') (split→∈-split-r s')

-- THE ACTION ON A CLAUSE FAMILY
--
-- A handler's clauses close over the *eternal* part of the context, so the
-- action reaches them restricted: each zone contributes `restrict-ren` of its
-- own renaming, or — at the substituting zones — `⟨_⟩[_↦_]cl`, which is why this
-- is stated on a whole family rather than one clause. There is no closed form
-- for it in terms of `env-Cˢ`: `env-clause γ St` will not do, its action landing
-- over `toCtx St` where the `handle` former wants `(Γ ++ᶜ Δ) ᴱ`.

env-Hˢ : ∀ {St Γ B} → (γ : Env St Γ) → (Δ : Ctx)
       → Fam B ((Γ ++ᶜ Δ) ᴱ) → Fam B ((toCtx St ++ᶜ Δ) ᴱ)

env-Hˢ ⌊ St ⌋ Δ K = K

env-Hˢ (∅ᵉ St) Δ K op ε =
  C-rename (cong-∷-ren (cong-∷-ren
             (restrict-ren (cong-ren {Γ'' = Δ} (∅-ren St))))) (K op ε)

env-Hˢ (sliceᵉ γ q) Δ K op ε =
  C-rename (cong-∷-ren (cong-∷-ren
             (restrict-ren (cong-ren {Γ'' = Δ} (slice-renᵘ q)))))
    (env-Hˢ γ Δ K op ε)

env-Hˢ {B = B} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ K op ε =
  C-rename (cong-∷-ren (cong-∷-ren
             (restrict-ren (cong-ren {Γ'' = Δ} (unbox-ren q)))))
    (Cl-cast op ε (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))
      (env-Hˢ γ ([] ⟨ ρ ⟩ ++ᶜ Δ)
        (λ op' ε' → Cl-cast op' ε' (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) (K op' ε'))
        op ε))

env-Hˢ {B = B} (liftᵉ {St = St} {Γ = Γ} {A = A} {ρ = ρ} V γ) Δ K op ε =
  Cl-cast op ε (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))
    (env-Hˢ γ ([] ∷ [ ρ ] A ++ᶜ Δ)
      (λ op' ε' → Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) (K op' ε'))
      op ε)

env-Hˢ {B = B} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ K op ε =
  Cl-cast op ε (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    (⟨ eternal? A ⟩[ split→∈ t ↦ castᵛ (sym (split→∈-split-l t)) W ]cl
       (λ op' ε' →
          Cl-cast op' ε' (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
            (env-Hˢ γ ([] ∷ A ++ᶜ Δ)
              (λ op'' ε'' → Cl-cast op'' ε'' (++ᶜ-assoc Γ ([] ∷ A) Δ)
                              (K op'' ε''))
              op' ε'))
       op ε)
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}

env-Hˢ {B = B} (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ K op ε =
  env-Hˢ γ Δ
    (λ op' ε' →
       env-eternal-H {Δ₀} {Γ₁ ++ᶜ Δ} {B} lf η
         (λ op'' ε'' → Cl-cast op'' ε'' (++ᶜ-assoc Δ₀ Γ₁ Δ) (K op'' ε''))
         op' ε')
    op ε

-- THE ACTION COMMUTES WITH `handle`
--
-- The last of the structural laws. Its clauses need no eternality dispatch —
-- renaming maps `handle` to `handle` and so does `_[_↦_]c`, its split having
-- moved into `⟨_⟩[_↦_]cl` — and `env-Hˢ`'s transports are `Cl-cast`, which is
-- exactly what `cast-handle` produces, so the two sides meet on the nose.

env-Cˢ-handle : ∀ {St Γ A B ε ε'} → (γ : Env St Γ) → (Δ : Ctx)
              → (M : (Γ ++ᶜ Δ) ⊢C⦂ A ‼ ε)
              → (H : Fam B ((Γ ++ᶜ Δ) ᴱ))
              → (N : (Γ ++ᶜ Δ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε')
              → env-Cˢ γ Δ (handle M `with H `in N)
              ≡ handle (env-Cˢ γ Δ M)
                 `with env-Hˢ γ Δ H
                 `in (env-Cˢ γ (Δ ⟨ mapᵉ ε ⟩ ∷ A) N)

env-Cˢ-handle ⌊ St ⌋ Δ M H N = refl
env-Cˢ-handle (∅ᵉ St) Δ M H N = refl
env-Cˢ-handle (sliceᵉ γ q) Δ M H N =
  cong (C-rename (cong-ren (slice-renᵘ q))) (env-Cˢ-handle γ Δ M H N)

env-Cˢ-handle {A = A} {ε = ε} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ M H N =
  cong (C-rename (cong-ren (unbox-ren q)))
    (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-handle ei))
      (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' (handle _ `with _ `in z)))
                   (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) ei) ei₂ N))
        (trans (cong (castᶜ eo) (env-Cˢ-handle γ Δ' _ _ _))
          (trans (cast-handle eo)
                 (cong (λ z → handle _ `with _ `in z)
                       (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eo) eo₂ _))))))
  where
    Δ'  = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei  = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) (Δ ⟨ mapᵉ ε ⟩ ∷ A)

env-Cˢ-handle {A = A} {ε = ε}
              (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ M H N =
  trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' z)) (cast-handle ei))
    (trans (cong (λ z → castᶜ eo (env-Cˢ γ Δ' (handle _ `with _ `in z)))
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) ei) ei₂ N))
      (trans (cong (castᶜ eo) (env-Cˢ-handle γ Δ' _ _ _))
        (trans (cast-handle eo)
               (cong (λ z → handle _ `with _ `in z)
                     (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eo) eo₂ _)))))
  where
    Δ'  = [] ∷ [ ρ ] A₀ ++ᶜ Δ
    eo  = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A₀) Δ)
    ei  = ++ᶜ-assoc Γ ([] ∷ [ ρ ] A₀) Δ
    eo₂ = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    ei₂ = ++ᶜ-assoc Γ ([] ∷ [ ρ ] A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A)

env-Cˢ-handle {A = A} {B = B} {ε = ε} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ M H N =
  trans (cong (λ z → castᶜ eOut ((castᶜ eIn (env-Cˢ γ Δ' z)) [ x ↦ Ŵ ]c))
              (cast-handle eA))
    (trans (cong (λ z → castᶜ eOut
                          ((castᶜ eIn (env-Cˢ γ Δ' (handle Mi `with Hi `in z)))
                             [ x ↦ Ŵ ]c))
                 (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eA) eA₂ N))
      (trans (cong (λ z → castᶜ eOut ((castᶜ eIn z) [ x ↦ Ŵ ]c))
                   (env-Cˢ-handle γ Δ' _ _ _))
        (trans (cong (λ z → castᶜ eOut (z [ x ↦ Ŵ ]c)) (cast-handle eIn))
          (trans (cong (λ z → castᶜ eOut
                                ((handle (castᶜ eIn Mγ) `with Hγc `in z)
                                   [ x ↦ Ŵ ]c))
                       (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eIn)
                                  eIn₂ Nγ))
            (trans (cast-handle eOut)
                   (cong (λ z → handle (castᶜ eOut ((castᶜ eIn Mγ) [ x ↦ Ŵ ]c))
                                 `with Hγo `in z)
                         (castᶜ-irr (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) eOut)
                                    eOut₂ _)))))))
  where
    t     = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    x     = split→∈ t
    Ŵ     = castᵛ (sym (split→∈-split-l t)) W
    Δ'    = [] ∷ A₀ ++ᶜ Δ
    eIn   = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA    = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eOut  = cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t)
    t₂    = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ ⟨ mapᵉ ε ⟩ ∷ A}
    eIn₂  = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A))
    eA₂   = ++ᶜ-assoc Γ ([] ∷ A₀) (Δ ⟨ mapᵉ ε ⟩ ∷ A)
    eOut₂ = cong₂ _++ᶜ_ (split→∈-split-l t₂) (split→∈-split-r t₂)

    Mi  = castᶜ eA M
    Hi  = λ op ε₀ → Cl-cast op ε₀ eA (H op ε₀)
    Mγ  = env-Cˢ γ Δ' Mi
    Hγ  = env-Hˢ γ Δ' Hi
    Nγ  = env-Cˢ γ (Δ' ⟨ mapᵉ ε ⟩ ∷ A) (castᶜ eA₂ N)
    Hγc = λ op ε₀ → Cl-cast op ε₀ eIn (Hγ op ε₀)
    Hγo = λ op ε₀ →
            Cl-cast op ε₀ eOut
              (⟨ eternal? A₀ ⟩[ x ↦ Ŵ ]cl Hγc op ε₀)

env-Cˢ-handle {A = A} {ε = ε} (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ M H N =
  trans (cong (λ z → env-Cˢ γ Δ (env-eternal-C lf η z)) (cast-handle eA))
    (trans (cong (λ z → env-Cˢ γ Δ
                          (env-eternal-C lf η (handle _ `with _ `in z)))
                 (castᶜ-irr (cong (λ Γ₁' → Γ₁' ⟨ mapᵉ ε ⟩ ∷ A) eA) eA₂ N))
      (trans (cong (env-Cˢ γ Δ) (env-eternal-handle lf η _ _ _))
             (env-Cˢ-handle γ Δ _ _ _)))
  where
    eA  = ++ᶜ-assoc Δ₀ Γ₁ Δ
    eA₂ = ++ᶜ-assoc Δ₀ Γ₁ (Δ ⟨ mapᵉ ε ⟩ ∷ A)

-- THE ETERNAL RESTRICTION OF AN ENVIRONMENT
--
-- A handler clause closes over `Γ ᴱ` (`Language.agda:153`), so the `handle`
-- case of the fundamental lemma needs closed values for it. They are there:
-- the state contributes nothing (`toCtxᴱ-[]` — cells are box-typed, never
-- eternal), an eternal-typed telescope entry is a value over `toCtx St` of
-- eternal type and so *is* closed (`eternal-val-restrict`), and the eternal
-- prefix already holds closed values.

-- A variable of the eternal restriction comes from the context itself
-- (`∈-ᴱ⁻`, in `Syntax.Renamings.Equivalence`), and every variable of the
-- eternal restriction has eternal type.

ᴱ-eternal : ∀ {A ρ} → (Δ : Ctx) → A ∈[ ρ ] Δ ᴱ → Eternal A
ᴱ-eternal []        x with x
... | ()
ᴱ-eternal (Δ ∷ B)   x with eternal? B
ᴱ-eternal (Δ ∷ B)   Hd       | yes et = et
ᴱ-eternal (Δ ∷ B)   (Tl-∷ y) | yes _  = ᴱ-eternal Δ y
ᴱ-eternal (Δ ∷ B)   x        | no  _  = ᴱ-eternal Δ x
ᴱ-eternal (Δ ⟨ ρ ⟩) x = ᴱ-eternal Δ x

env-ᴱ   : ∀ {St Γ} → (γ : Env St Γ) → ClosedVals (Γ ᴱ)

-- as `ᴱ-lock-free-∷`: the telescope entry's decision is taken as an
-- argument, so a caller that has decided it sees the values reduce
env-ᴱ-∷ : ∀ {St Γ A} → (γ : Env St Γ) → (V : toCtx St ⊢V⦂ A)
        → (d : Dec (Eternal A)) → ClosedVals (ᴱ-∷ (Γ ᴱ) A d)

env-ᴱ-∷ {St = St} γ V (yes et) Hd       =
  castᵛ (toCtxᴱ-[] St) (eternal-val-restrict et V)
env-ᴱ-∷           γ V (yes et) (Tl-∷ y) = env-ᴱ γ y
env-ᴱ-∷           γ V (no ¬et) x        = env-ᴱ γ x


env-ᴱ ⌊ St ⌋ x =
  ⊥-elim (not-in-empty-ctx (subst (λ Γ' → _ ∈[ _ ] Γ') (toCtxᴱ-[] St) x))
env-ᴱ (∅ᵉ St) x = ⊥-elim (not-in-empty-ctx x)
-- a cell's type is a box type, never eternal, so the prefix is unchanged
env-ᴱ (liftᵉ {A = A} {ρ = ρ} V γ) x with eternal? ([ ρ ] A)
... | yes ()
... | no ¬et = env-ᴱ γ x
env-ᴱ (γ ⟨ q ⟩ᵉ) x = env-ᴱ γ x
env-ᴱ (sliceᵉ γ q) x = env-ᴱ γ x
env-ᴱ (_∷ᵉ_ {A = A} γ V) = env-ᴱ-∷ γ V (eternal? A)
env-ᴱ (eternalˡ {Γ = Γ} Δ lf η γ) x
  with ∈-++ᶜ-split (Δ ᴱ) (Γ ᴱ) (subst (λ Γ' → _ ∈[ _ ] Γ') (ᴱ-++ᶜ Δ Γ) x)
... | inj₁ (ρ' , y) = η (proj₂ (∈-ᴱ⁻ Δ y))
... | inj₂ y        = env-ᴱ γ y

-- A CLAUSE'S CLOSING ENVIRONMENT, AT ANY STATE
--
-- What `∅ᵉ` is for. A handler clause closes over `Γ ᴱ`, whose values are the
-- closed ones `env-ᴱ` supplies; the state contributes nothing, so its zone is
-- `∅ᵉ` and the reducibility asks for no store. Routing through `⌊ St₁ ⌋` instead
-- would demand `Store St₁`, for cells the clause cannot mention.

env-clause : ∀ {St Γ} → (γ : Env St Γ) → (St₁ : 𝕊 []) → Env St₁ (Γ ᴱ)
env-clause {Γ = Γ} γ St₁ =
  eternalˡ (Γ ᴱ) (ᴱ-lock-free Γ) (env-ᴱ γ) (∅ᵉ St₁)

env-clause-rel : ∀ {St Γ} → (γ : Env St Γ) → (St₁ : 𝕊 [])
               → Rel-Env (env-clause γ St₁)
env-clause-rel {Γ = Γ} γ St₁ = tt , ᴱ-eternal Γ

-- THE CLAUSE ACTION AGAINST THE CLAUSE ENVIRONMENT
--
-- `env-Hˢ γ Δ` reaches a clause zone by zone, each contributing its own
-- `restrict-ren` or — at the substituting zones — its `⟨_⟩[_↦_]cl`, and the
-- weakening into a state's context comes only afterwards (`Fired`).
-- `env-clause γ St₁` instead substitutes every closed value `env-ᴱ γ` computes
-- and weakens once, at the base. The two agree, and only up to `≐ᶜ`: lining them
-- up moves each zone's renaming past the substitutions to its right, which
-- `Ren` being unquotiented does not do on the nose.
--
-- It is proved at the end of this module (`env-Hˢ-clause`), on the two
-- developments that go before it there: `sub-swap`, since the `_∷ᵉ_` zone
-- substitutes *after* the zones to its left while `env-eternal-C`
-- substitutes before; and `env-Hˢ-ᴱ`, the state-free core.

-- A state contributes nothing to a restriction, at any suffix.

toCtxᴱ-++ᶜ : (St : 𝕊 []) → (Δ : Ctx) → (toCtx St ++ᶜ Δ) ᴱ ≡ Δ ᴱ
toCtxᴱ-++ᶜ St Δ =
  trans (ᴱ-++ᶜ (toCtx St) Δ)
        (trans (cong (_++ᶜ Δ ᴱ) (toCtxᴱ-[] St)) (++ᶜ-identityˡ {Δ ᴱ}))

-- The weakening `env-clause` ends with, at a suffix.

clause-ren : (St₁ : 𝕊 []) → (Δ : Ctx) → Ren [] (Δ ᴱ) (toCtx St₁ ++ᶜ Δ ᴱ)
clause-ren St₁ Δ =
  cong-ren {Γ'' = Δ ᴱ} (∅-ren St₁) ∘ʳ eq-ren (sym (++ᶜ-identityˡ {Δ ᴱ}))

-- Relocating a clause along an equality of the *restricted* context it is
-- already stated over — `Cl-cast`'s shape, one `_ᴱ` further in.

Cl-castᴿ : ∀ {Γ₀ Γ₀' B} → (op : Op) → (ε : E) → Γ₀ ≡ Γ₀'
         → Cl B op ε Γ₀ → Cl B op ε Γ₀'
Cl-castᴿ {B = B} op ε e X =
  castᶜ (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              e)
        X

------------------------------------------------------------------------
-- FUNCTORIALITY IN THE STATE
--
-- `BOX` steps `⟨St, box V M⟩ ↝ ⟨St ∷ₛ V', M⟩`, so the `box` case of the
-- fundamental lemma must move an environment to the extended state. The term
-- needs no reindexing — `toCtx (St ∷ₛ V) = toCtx St ∷ [ρ]A` is the context the
-- action already produced, and moving the environment is recording the
-- allocation slice.
------------------------------------------------------------------------

env-alloc : ∀ {St Γ A ρ} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
          → Env St Γ
          ---------------------
          → Env (St ∷ₛ V) Γ

env-alloc V γ = sliceᵉ γ (alloc-slice V)

-- Reducibility is unaffected: the values still live at the earlier state.

env-allocᴿ : ∀ {St Γ A ρ} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
           → (γ : Env St Γ) → Rel-Env γ
           ------------------------------
           → Rel-Env (env-alloc V γ)

env-allocᴿ V γ pγ = pγ

------------------------------------------------------------------------
-- THE ACTION RESPECTS THE TERM EQUIVALENCE
--
-- Recursion on the environment, not on the term: each zone acts by renaming
-- and substitution, both of which are congruences (`V-rename-cong`, `sub-≐ᵛ`).
------------------------------------------------------------------------

env-eternal-V-≐ : ∀ {Δ Γ A} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → {V V' : (Δ ++ᶜ Γ) ⊢V⦂ A} → V ≐ᵛ V'
                → env-eternal-V lf η V ≐ᵛ env-eternal-V lf η V'

env-eternal-V-≐ lf-[]              η eV = castᵛ-≐ ++ᶜ-identityˡ eV
env-eternal-V-≐ {Δ ∷ B} {Γ} (lf-∷ lf) η eV =
  env-eternal-V-≐ lf (λ x → η (Tl-∷ x))
    (castᵛ-≐ _ (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Δ ∷ B} {Γ})) (≐ᵛ-refl _) eV))

env-Vˢ-≐ : ∀ {St Γ A} → (γ : Env St Γ) → (Δ : Ctx) → {V V' : (Γ ++ᶜ Δ) ⊢V⦂ A}
         → V ≐ᵛ V' → env-Vˢ γ Δ V ≐ᵛ env-Vˢ γ Δ V'

env-Vˢ-≐ ⌊ St ⌋       Δ eV = eV
env-Vˢ-≐ (∅ᵉ St)       Δ eV = V-rename-cong _ eV
env-Vˢ-≐ (sliceᵉ γ q) Δ eV = V-rename-cong _ (env-Vˢ-≐ γ Δ eV)
env-Vˢ-≐ (γ ⟨ q ⟩ᵉ)    Δ eV =
  V-rename-cong _ (castᵛ-≐ _ (env-Vˢ-≐ γ _ (castᵛ-≐ _ eV)))
env-Vˢ-≐ (liftᵉ V γ)   Δ eV = castᵛ-≐ _ (env-Vˢ-≐ γ _ (castᵛ-≐ _ eV))
env-Vˢ-≐ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ eV =
  castᵛ-≐ (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl (castᵛ (sym (split→∈-split-l t)) W))
      (castᵛ-≐ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
        (env-Vˢ-≐ γ ([] ∷ A ++ᶜ Δ) (castᵛ-≐ (++ᶜ-assoc Γ ([] ∷ A) Δ) eV))))
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}
env-Vˢ-≐ (eternalˡ Δ₀ lf η γ) Δ eV =
  env-Vˢ-≐ γ Δ (env-eternal-V-≐ lf η (castᵛ-≐ _ eV))


-- The eternal zone leaves the variables of the context it prefixes alone: each
-- of its substitutions replaces a variable of its own prefix (`sub-var-r`).

env-eternal-V-var-r : ∀ {Δ₀ Γ' A ρ} → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                    → (x : A ∈[ ρ ] Γ') → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                    → env-eternal-V lf η (var f (∈-++ᶜʳ {Γ = Δ₀} x)) ≐ᵛ var f' x

env-eternal-V-var-r lf-[] η x f f' =
  ≐ᵛ-trans (≡→≐ᵛ (trans (castᵛ-var ++ᶜ-identityˡ f (∈-++ᶜʳ x))
                        (cong (var f) (∈-++ᶜʳ-[] x))))
           var-≐

env-eternal-V-var-r (lf-∷ lf) η x f f' =
  ≐ᵛ-trans (env-eternal-V-≐ lf (λ z → η (Tl-∷ z)) (sub-var-r _ x _ f f))
           (env-eternal-V-var-r lf (λ z → η (Tl-∷ z)) x f f')



-- THE ACTION FIXES A SUFFIX VARIABLE
--
-- Recursion on the environment. Each zone either renames along a congruence
-- renaming (`ren-var-r`) or substitutes at a variable of the prefix
-- (`sub-var-r`); the two zones that re-bracket the suffix pass through
-- `∈-++ᶜʳ-assoc`.

env-Vˢ-var-r : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx) → (x : A ∈[ ρ ] Δ)
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → env-Vˢ γ Δ (var f (∈-++ᶜʳ {Γ = Γ} x))
             ≐ᵛ var f' (∈-++ᶜʳ {Γ = toCtx St} x)

env-Vˢ-var-r ⌊ St ⌋ Δ x f f' = var-≐
env-Vˢ-var-r (∅ᵉ St) Δ x f f' = ren-var-r (∅-ren St) x f f'

env-Vˢ-var-r (sliceᵉ γ q) Δ x f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren (slice-renᵘ q)) (env-Vˢ-var-r γ Δ x f f))
           (ren-var-r (slice-renᵘ q) x f f')

env-Vˢ-var-r (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ} γ q) Δ x f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren (unbox-ren q)) step)
           (ren-var-r (unbox-ren q) x f f')
  where
    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
    ei = ++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ
    y  = ∈-++ᶜʳ {Γ = [] ⟨ ρ ⟩} x

    inner : castᵛ ei (var f (∈-++ᶜʳ {Γ = Γ ⟨ ρ ⟩} x))
          ≡ var f (∈-++ᶜʳ {Γ = Γ} y)
    inner = trans (castᵛ-var ei f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Γ ([] ⟨ ρ ⟩) x))

    outer : castᵛ eo (var f (∈-++ᶜʳ {Γ = toCtx St} y))
          ≡ var f (∈-++ᶜʳ {Γ = toCtx St ⟨ ρ ⟩} x)
    outer =
      trans (castᵛ-var eo f (∈-++ᶜʳ y))
        (cong (var f)
          (trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) eo)
                       (sym (∈-++ᶜʳ-assoc (toCtx St) ([] ⟨ ρ ⟩) x)))
                 (subst-sym-subst′ (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ)
                                   (∈-++ᶜʳ x))))

    step : castᵛ eo (env-Vˢ γ Δ' (castᵛ ei (var f (∈-++ᶜʳ {Γ = Γ ⟨ ρ ⟩} x))))
         ≐ᵛ var f (∈-++ᶜʳ {Γ = toCtx St ⟨ ρ ⟩} x)
    step =
      ≐ᵛ-trans (≡→≐ᵛ (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) inner))
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ Δ' y f f)) (≡→≐ᵛ outer))

env-Vˢ-var-r (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ} V γ) Δ x f f' =
  ≐ᵛ-trans (≡→≐ᵛ (cong (λ z → castᵛ eo (env-Vˢ γ Δ' z)) inner))
    (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ Δ' y f f))
      (≐ᵛ-trans (≡→≐ᵛ outer) var-≐))
  where
    Δ₁ = [] ∷ [ ρ ] A₀
    Δ' = Δ₁ ++ᶜ Δ
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    y  = ∈-++ᶜʳ {Γ = Δ₁} x

    inner : castᵛ ei (var f (∈-++ᶜʳ {Γ = Γ ∷ [ ρ ] A₀} x))
          ≡ var f (∈-++ᶜʳ {Γ = Γ} y)
    inner = trans (castᵛ-var ei f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Γ Δ₁ x))

    outer : castᵛ eo (var f (∈-++ᶜʳ {Γ = toCtx St} y))
          ≡ var f (∈-++ᶜʳ {Γ = toCtx St ∷ [ ρ ] A₀} x)
    outer =
      trans (castᵛ-var eo f (∈-++ᶜʳ y))
        (cong (var f)
          (trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) eo)
                       (sym (∈-++ᶜʳ-assoc (toCtx St) Δ₁ x)))
                 (subst-sym-subst′ (++ᶜ-assoc (toCtx St) Δ₁ Δ) (∈-++ᶜʳ x))))

env-Vˢ-var-r (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ x f f' =
  ≐ᵛ-trans (≡→≐ᵛ (cong (λ z → castᵛ (castOf Δ)
                                (castᵛ eIn (env-Vˢ γ Δ'' z) [ split→∈ t ↦ Ŵ ]v))
                       inner))
    (≐ᵛ-trans
      (castᵛ-≐ (castOf Δ)
        (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl Ŵ)
          (≐ᵛ-trans (castᵛ-≐ eIn (env-Vˢ-var-r γ Δ'' y f f)) (≡→≐ᵛ outer))))
      (sub-var-r Δ x Ŵ f f'))
  where
    Δ'' = [] ∷ A₀ ++ᶜ Δ
    eIn = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    eA  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    t   = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    Ŵ   = castᵛ (sym (split→∈-split-l t)) W
    y   = ∈-++ᶜʳ {Γ = [] ∷ A₀} x

    inner : castᵛ eA (var f (∈-++ᶜʳ {Γ = Γ ∷ A₀} x))
          ≡ var f (∈-++ᶜʳ {Γ = Γ} y)
    inner = trans (castᵛ-var eA f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Γ ([] ∷ A₀) x))

    outer : castᵛ eIn (var f (∈-++ᶜʳ {Γ = toCtx St} y))
          ≡ var f (∈-++ᶜʳ {Γ = toCtx St ∷ A₀} x)
    outer =
      trans (castᵛ-var eIn f (∈-++ᶜʳ y))
        (cong (var f)
          (trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) eIn)
                       (sym (∈-++ᶜʳ-assoc (toCtx St) ([] ∷ A₀) x)))
                 (subst-sym-subst′ (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
                                   (∈-++ᶜʳ x))))

env-Vˢ-var-r (eternalˡ {Γ = Γ} Δ₀ lf η γ) Δ x f f' =
  ≐ᵛ-trans
    (env-Vˢ-≐ γ Δ
      (≐ᵛ-trans (≡→≐ᵛ (cong (env-eternal-V lf η) inner))
                (env-eternal-V-var-r lf η (∈-++ᶜʳ {Γ = Γ} x) f f)))
    (env-Vˢ-var-r γ Δ x f f')
  where
    inner : castᵛ (++ᶜ-assoc Δ₀ Γ Δ) (var f (∈-++ᶜʳ {Γ = Δ₀ ++ᶜ Γ} x))
          ≡ var f (∈-++ᶜʳ {Γ = Δ₀} (∈-++ᶜʳ {Γ = Γ} x))
    inner = trans (castᵛ-var (++ᶜ-assoc Δ₀ Γ Δ) f (∈-++ᶜʳ x))
                  (cong (var f) (∈-++ᶜʳ-assoc Δ₀ Γ x))

------------------------------------------------------------------------
-- THE ACTION ON A VARIABLE
--
-- What each zone does to a variable of its own context. The bounds are left
-- free: `_≐ᵛ_` does not see them, and each caller has its own.
------------------------------------------------------------------------

-- A telescope entry is substituted by its value: at the empty suffix the
-- action is `env-Vˢ γ ([] ∷ A)` followed by substituting `Hd`, and the entry's
-- own variable is a suffix variable.

env-var-hd : ∀ {St Γ A} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A)
           → (f : ¬ Eternal A → uᵣ ≾ᵣ uᵣ)
           → env-V (γ ∷ᵉ W) (var f Hd) ≐ᵛ W
env-var-hd γ W f =
  sub-≐ᵛ Hd (≐ᵛ-refl W) (env-Vˢ-var-r γ ([] ∷ _) Hd f f)

-- Any other variable is untouched by the entry, and is the action of the rest.
--
-- Both are the same lemma at a one-entry suffix: the action under a suffix `Δ`
-- of a variable of the *prefix* is the action at the empty suffix, pushed under
-- `Δ` by `push-ren`. The suffix must be arbitrary, because `env-Vˢ` grows it at
-- `_⟨_⟩ᵉ` and `_∷ᵉ_`; `push-ren` is pinned up to `_≐ʳ_` by `push-ren-tgt`, which
-- is why no renaming needs to be quantified over.
--
-- The two zones that grow the suffix use the induction hypothesis **twice** —
-- at `[] ∷ A ++ᶜ Δ` (resp. `[] ⟨ ρ ⟩ ++ᶜ Δ`) for the goal's left side and at
-- `[] ∷ A` (resp. `[] ⟨ ρ ⟩`) for its right, whose own action is at suffix `[]`.
-- Both land on the same `env-Vˢ γ [] (var _ x)`, leaving an equation between two
-- composite renamings, which `push-ren-++ᶜ` and `push-ren-nat` settle.
--
-- `¬ Eternal A` is what makes the lock case go through: it supplies the lock's
-- own bound by `≾ᵣ-zero-product*`, where at an eternal type `f` is vacuous. It
-- also rules out `eternalˡ`'s prefix, whose every variable is eternal — which is
-- what `Eternal-Env` is for.

env-Vˢ-var-l : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → Eternal-Env γ → ¬ Eternal A
             → (p : ctx-grade Δ ≾ᵣ uᵣ)
             → (x : A ∈[ ρ ] Γ)
             → (f  : ¬ Eternal A → grade-++ᶜˡ ρ Δ ≾ᵣ uᵣ)
             → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → env-Vˢ γ Δ (var f (∈-++ᶜˡ Δ x))
             ≐ᵛ V-rename (push-ren Δ p) (env-Vˢ γ [] (var f' x))

env-Vˢ-var-l ⌊ St ⌋ Δ eγ ¬et p x f f' =
  ≐ᵛ-sym (var-ren-tgt-≐ (push-ren Δ p) x f' (push-ren-tgt Δ p x) f)

env-Vˢ-var-l (∅ᵉ St) Δ eγ ¬et p x f f' = ⊥-elim (not-in-empty-ctx x)

env-Vˢ-var-l (sliceᵉ γ q) Δ eγ ¬et p x f f' =
  ≐ᵛ-trans
    (V-rename-cong (cong-ren {Γ'' = Δ} (slice-renᵘ q))
                   (env-Vˢ-var-l γ Δ eγ ¬et p x f f'))
    (≐ᵛ-trans
      (≐ᵛ-sym (V-rename-∘ (cong-ren {Γ'' = Δ} (slice-renᵘ q)) (push-ren Δ p) _))
      (≐ᵛ-trans (V-rename-≐ (push-ren-nat (slice-renᵘ q) Δ p) _)
                (V-rename-∘ (push-ren Δ p) (slice-renᵘ q) _)))

env-Vˢ-var-l (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₁} γ q) Δ eγ ¬et p (Tl-⟨⟩ x) f f' =
  ≐ᵛ-trans
    (V-rename-cong (cong-ren {Γ'' = Δ} (unbox-ren q))
      (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) eγ ¬et p₁ x f₁ f''))
          (≐ᵛ-trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
            (≐ᵛ-trans (V-rename-≐ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
                      (V-rename-∘ (push-ren Δ p) (push-ren Δ₁ pₗ) _))))))
    (≐ᵛ-trans
      (≐ᵛ-sym (V-rename-∘ (cong-ren {Γ'' = Δ} (unbox-ren q)) (push-ren Δ p) _))
      (≐ᵛ-trans (V-rename-≐ (push-ren-nat (unbox-ren q) Δ p) _)
        (≐ᵛ-trans (V-rename-∘ (push-ren Δ p) (unbox-ren q) _)
          (V-rename-cong (push-ren Δ p)
            (V-rename-cong (unbox-ren q)
              (≐ᵛ-sym (env-Vˢ-var-l γ Δ₁ eγ ¬et pₗ x f' f'')))))))
  where
    Δ₁ = [] ⟨ ρ₁ ⟩
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

    pρ = ≾ᵣ-zero-productʳ (grade-++ᶜˡ-zeroˡ Δ (f ¬et))
    pₗ = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ₁)) pρ
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁  = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)
    f'' = λ z → ≾ᵣ-zero-productˡ (grade-++ᶜˡ-zeroˡ Δ (f z))

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Tgt-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The cell zone: nothing is substituted, so both sides re-bracket and the
-- comparison is `push-ren-++ᶜ` alone.

env-Vˢ-var-l (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₁} V γ) Δ eγ ¬et p (Tl-∷ x) f f' =
  ≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
    (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) eγ ¬et p₁ x f₁ f'))
      (≐ᵛ-trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
        (≐ᵛ-trans (V-rename-≐ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
          (≐ᵛ-trans (V-rename-∘ (push-ren Δ p) (push-ren Δ₁ pₗ) _)
            (V-rename-cong (push-ren Δ p)
              (≐ᵛ-sym (env-Vˢ-var-l γ Δ₁ eγ ¬et pₗ x f' f')))))))
  where
    Δ₁ = [] ∷ [ ρ₁ ] A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ

    pₗ = ≾ᵣ-refl
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁ = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Tgt-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The cell's own variable: a *suffix* variable of the inner action, carried
-- through unchanged since nothing is substituted.

env-Vˢ-var-l (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₁} V γ) Δ eγ ¬et p Hd f f' =
  ≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
    (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ (Δ₁ ++ᶜ Δ) hd f f))
      (≐ᵛ-trans outer
        (≐ᵛ-sym
          (≐ᵛ-trans
            (V-rename-cong (push-ren Δ p)
              (env-Vˢ-var-r γ Δ₁ (Hd {Γ = []}) f' f'))
            (var-ren-tgt-≐ (push-ren Δ p) (Hd {Γ = toCtx St}) f'
                           (push-ren-tgt Δ p Hd) f)))))
  where
    Δ₁ = [] ∷ [ ρ₁ ] A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    hd = ∈-++ᶜˡ {Γ = Δ₁} Δ (Hd {Γ = []})

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Γ} (Hd {Γ = []})))
              (∈-++ᶜʳ {Γ = Γ} hd) (∈-++ᶜˡ-++ᶜʳ Γ Δ₁ Δ (Hd {Γ = []})) f f

    outer = castᵛ-var-Tgt eo (∈-++ᶜʳ {Γ = toCtx St} hd)
              (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
              (Tgt-cast-flip (++ᶜ-assoc (toCtx St) Δ₁ Δ) _ _
                             (∈-++ᶜˡ-++ᶜʳ (toCtx St) Δ₁ Δ (Hd {Γ = []})))
              f f

env-Vˢ-var-l (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ eγ ¬et p (Tl-∷ x) f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {toCtx St} {A₀} Δ)
      (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl _)
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
          (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-l γ (Δ₁ ++ᶜ Δ) eγ ¬et p₁ x f₁ f'))
            (≐ᵛ-trans (castᵛ-rename eo (push-ren (Δ₁ ++ᶜ Δ) p₁) _)
              (≐ᵛ-trans (V-rename-≐ (push-ren-++ᶜ Δ₁ Δ p₁ pₗ p) _)
                (≐ᵛ-trans
                  (V-rename-≐
                    (≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (push-ren-∷ pₗ))
                              (≐ʳ-sym (push-ren-nat wk-ren Δ p))) _)
                  (V-rename-∘ (cong-ren {Γ'' = Δ} wk-ren) (push-ren Δ p) _))))))))
    (≐ᵛ-trans (sub-wk-V Δ (V-rename (push-ren Δ p) Z) _)
      (V-rename-cong (push-ren Δ p)
        (≐ᵛ-sym
          (≐ᵛ-trans
            (castᵛ-≐ (castOf {toCtx St} {A₀} [])
              (sub-≐ᵛ (split→∈ t₀) (≐ᵛ-refl _)
                (≐ᵛ-trans (env-Vˢ-var-l γ Δ₁ eγ ¬et pₗ x f' f')
                          (V-rename-≐ (push-ren-∷ pₗ) _))))
            (sub-wk-V [] Z _)))))
  where
    Δ₁ = [] ∷ A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    t  = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    t₀ = split-≡-++ᶜ {toCtx St ∷ A₀} {[]}
    Z  = env-Vˢ γ [] (var f' x)

    pₗ = ≾ᵣ-refl
    p₁ = ctx-grade-++ᶜ-≾ᵣ Δ₁ Δ pₗ p

    f₁ = λ z → subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ Δ₁ Δ)) (f z)

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜˡ Δ₁ x)) (∈-++ᶜˡ (Δ₁ ++ᶜ Δ) x)
              (Tgt-cast-flip⁻ ei _ _ (∈-++ᶜˡ-assoc Δ₁ Δ x)) f f₁

-- The entry's own variable: a *suffix* variable of the inner action, which the
-- substitution then hits (`sub-var-hit′`), returning the entry's value pushed
-- under `Δ`. At the empty suffix that is `env-var-hd`.

env-Vˢ-var-l (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ eγ ¬et p Hd f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {toCtx St} {A₀} Δ)
      (sub-≐ᵛ (split→∈ t) (≐ᵛ-refl _)
        (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-≐ γ (Δ₁ ++ᶜ Δ) inner))
          (≐ᵛ-trans (castᵛ-≐ eo (env-Vˢ-var-r γ (Δ₁ ++ᶜ Δ) hd f f))
                    outer))))
    (≐ᵛ-trans
      (sub-var-hit′ Δ ¬et p (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
                    (sym (split→∈-∈-++ᶜˡ (toCtx St) A₀ Δ)) _ f)
      (≐ᵛ-trans (V-rename-cong (push-ren Δ p)
                  (≡→≐ᵛ (castᵛ-sym-cast (split→∈-split-l t) W)))
                (V-rename-cong (push-ren Δ p) (≐ᵛ-sym (env-var-hd γ W f')))))
  where
    Δ₁ = [] ∷ A₀
    eo = sym (++ᶜ-assoc (toCtx St) Δ₁ Δ)
    ei = ++ᶜ-assoc Γ Δ₁ Δ
    t  = split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}
    hd = ∈-++ᶜˡ {Γ = Δ₁} Δ (Hd {Γ = []})

    inner = castᵛ-var-Tgt ei (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Γ} (Hd {Γ = []})))
              (∈-++ᶜʳ {Γ = Γ} hd) (∈-++ᶜˡ-++ᶜʳ Γ Δ₁ Δ (Hd {Γ = []})) f f

    outer = castᵛ-var-Tgt eo (∈-++ᶜʳ {Γ = toCtx St} hd)
              (∈-++ᶜˡ Δ (Hd {Γ = toCtx St}))
              (Tgt-cast-flip (++ᶜ-assoc (toCtx St) Δ₁ Δ) _ _
                             (∈-++ᶜˡ-++ᶜʳ (toCtx St) Δ₁ Δ (Hd {Γ = []})))
              f f

-- An eternal prefix's variables are all eternal, so `¬ Eternal A` puts `x` in
-- the context it prefixes, where the prefix's substitutions leave it alone.

env-Vˢ-var-l (eternalˡ {Γ = Γ} Δ₀ lf η γ) Δ (eγ , et) ¬et p x f f'
  with ∈-++ᶜ-split Δ₀ Γ x in eq

... | inj₁ (ρ' , y) = ⊥-elim (¬et (et y))

... | inj₂ y
  rewrite ∈-++ᶜ-split-inj₂ Δ₀ Γ x y eq =
  ≐ᵛ-trans
    (env-Vˢ-≐ γ Δ
      (≐ᵛ-trans (env-eternal-V-≐ lf η inner)
                (env-eternal-V-var-r lf η (∈-++ᶜˡ {Γ = Γ} Δ y) f f)))
    (≐ᵛ-trans (env-Vˢ-var-l γ Δ eγ ¬et p y f f')
      (V-rename-cong (push-ren Δ p)
        (env-Vˢ-≐ γ []
          (≐ᵛ-sym (env-eternal-V-var-r lf η y f' f')))))
  where
    inner = castᵛ-var-Tgt (++ᶜ-assoc Δ₀ Γ Δ)
              (∈-++ᶜˡ Δ (∈-++ᶜʳ {Γ = Δ₀} y))
              (∈-++ᶜʳ {Γ = Δ₀} (∈-++ᶜˡ {Γ = Γ} Δ y))
              (∈-++ᶜˡ-++ᶜʳ Δ₀ Γ Δ y) f f

-- The two one-entry instances. `env-var-tl` substitutes `Hd` into a weakening,
-- which cancels (`sub-wk-V []`); `env-var-lock` composes the lock crossing with
-- the slice, which `unbox-ren-unit` recognises as the unit slice's renaming.

env-var-tl : ∀ {St Γ A A₀ ρ} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A₀)
           → Eternal-Env γ → ¬ Eternal A
           → (x : A ∈[ ρ ] Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → env-V (γ ∷ᵉ W) (var f (Tl-∷ x)) ≐ᵛ env-V γ (var f' x)

env-var-tl {St = St} {A₀ = A₀} γ W eγ ¬et x f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {toCtx St} {A₀} [])
      (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {toCtx St ∷ A₀} {[]})) (≐ᵛ-refl _)
        (≐ᵛ-trans (env-Vˢ-var-l γ ([] ∷ A₀) eγ ¬et ≾ᵣ-refl x f f')
                  (V-rename-≐ (push-ren-∷ ≾ᵣ-refl) _))))
    (sub-wk-V [] (env-Vˢ γ [] (var f' x)) _)

env-var-lock : ∀ {St St' Γ A ρ ρ'} → (γ : Env St Γ) → (q : Slice St ρ St' uᵣ)
             → Eternal-Env γ → ¬ Eternal A
             → (p : ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ' ] Γ)
             → (f  : ¬ Eternal A → ρ' ·ᵣ ρ ≾ᵣ uᵣ)
             → (f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
             → env-V (γ ⟨ q ⟩ᵉ) (var f (Tl-⟨⟩ x))
             ≐ᵛ slice-val (slice-unit q p) (env-V γ (var f' x))

-- The cell zone's own instance: `Δ := [] ∷ [ ρ ] A₀`, where the push is the
-- weakening past the new cell and there is nothing to cancel — `liftᵉ` keeps the
-- binder rather than substituting for it.

env-var-lift : ∀ {St Γ A A₀ ρ ρ'} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A₀)
             → (γ : Env St Γ) → Eternal-Env γ → ¬ Eternal A
             → (x : A ∈[ ρ' ] Γ) → (f f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
             → env-V (liftᵉ V γ) (var f (Tl-∷ x))
             ≐ᵛ V-rename wk-ren (env-V γ (var f' x))

env-var-lift {A₀ = A₀} {ρ = ρ} V γ eγ ¬et x f f' =
  ≐ᵛ-trans (env-Vˢ-var-l γ ([] ∷ [ ρ ] A₀) eγ ¬et ≾ᵣ-refl x f f')
           (V-rename-≐ (push-ren-∷ ≾ᵣ-refl) _)

env-var-lock {ρ = ρ} γ q eγ ¬et p x f f' =
  ≐ᵛ-trans
    (V-rename-cong (unbox-ren q)
      (env-Vˢ-var-l γ ([] ⟨ ρ ⟩) eγ ¬et pₗ x f f'))
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ (unbox-ren q) (push-ren ([] ⟨ ρ ⟩) pₗ) _))
              (V-rename-≐ (≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (push-ren-⟨⟩ pₗ p))
                                    (unbox-ren-unit q p)) _))
  where
    pₗ = ≾ᵣ-trans (≾ᵣ-reflexive (·ᵣ-identityˡ ρ)) p

-- The eternal zone does not touch the variables of the context it prefixes.
-- `y` must be *the* variable `x` comes from: quantifying over the two
-- independently would identify any two same-typed variables of a state
-- context, since `env-V ⌊ St ⌋` is the identity.

env-var-eternalˡ : ∀ {St Γ A ρ} → (Δ : Ctx) → (lf : Lock-free Δ)
                 → (η : ClosedVals Δ) → (γ : Env St Γ)
                 → (x : A ∈[ ρ ] (Δ ++ᶜ Γ)) → (y : A ∈[ ρ ] Γ)
                 → ∈-++ᶜ-split Δ Γ x ≡ inj₂ y
                 → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
                 → env-V (eternalˡ Δ lf η γ) (var f x) ≐ᵛ env-V γ (var f y)
env-var-eternalˡ Δ lf η γ x y eq f =
  env-Vˢ-≐ γ []
    (subst (λ z → env-eternal-V lf η (var f z) ≐ᵛ var f y)
           (sym (∈-++ᶜ-split-inj₂ Δ _ x y eq))
           (env-eternal-V-var-r lf η y f f))

-- Every variable of a reducible environment's context becomes a reducible
-- value: the fundamental lemma's variable case. The eternal cases are the two
-- that need no law — `Val` holds of everything at an eternal type, which is
-- also why a locked variable of eternal type needs no slice.

env-var : ∀ {St Γ A ρ} → (γ : Env St Γ) → Rel-Env γ
        → (x : A ∈[ ρ ] Γ) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
        ------------------------------------------------
        → Val A St (env-V γ (var f x))

env-var ⌊ St ⌋       pγ x f = store-var pγ x f

env-var (∅ᵉ St)       pγ x f = ⊥-elim (not-in-empty-ctx x)

env-var (sliceᵉ γ q) pγ x f = Val-slice q _ (env-var γ pγ x f)

env-var (γ ∷ᵉ W) (pγ , pW) Hd       f =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-hd γ W f)) pW
env-var {A = A} (γ ∷ᵉ W) (pγ , pW) (Tl-∷ x) f with eternal? A
... | yes et = Val-eternal et _
... | no ¬et =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-tl γ W (Rel-Env-eternal γ pγ) ¬et x f f))
           (env-var γ pγ x f)

env-var (liftᵉ V γ) (pγ , pV) Hd f =
  Val-≐ᵛ _ (≐ᵛ-sym (env-Vˢ-var-r γ ([] ∷ _) Hd f f)) (store-fresh V pV f)
env-var {A = A} (liftᵉ V γ) (pγ , pV) (Tl-∷ x) f with eternal? A
... | yes et = Val-eternal et _
... | no ¬et =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-lift V γ (Rel-Env-eternal γ pγ) ¬et x f f))
    (Val-≐ᵛ _ (V-rename-≐ (alloc-ren-≐ V) _)
      (Val-slice (alloc-slice V) _ (env-var γ pγ x f)))

env-var {A = A} (γ ⟨ q ⟩ᵉ) pγ (Tl-⟨⟩ x) f with eternal? A
... | yes et = Val-eternal et _
... | no ¬et =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-lock γ q (Rel-Env-eternal γ pγ) ¬et p x f f'))
           (Val-slice (slice-unit q p) _ (env-var γ pγ x f'))
  where
    p  = ≾ᵣ-zero-productʳ (f ¬et)
    f' = λ _ → ≾ᵣ-zero-productˡ (f ¬et)

env-var {A = A} (eternalˡ Δ lf η γ) (pγ , et) x f
  with ∈-++ᶜ-split Δ _ x in eq
... | inj₁ (ρ' , y) = Val-eternal (et y) _
... | inj₂ y        =
  Val-≐ᵛ _ (≐ᵛ-sym (env-var-eternalˡ Δ lf η γ x y eq f)) (env-var γ pγ y f)

------------------------------------------------------------------------
-- THE CLAUSE ACTION AGAINST THE CLAUSE ENVIRONMENT, PROVED
--
-- The factorisation: `env-Hˢ-ᴱ` is the state-free core — the clause
-- action *is* the eternal-restriction action `env-eternal-C ∘ env-ᴱ`, up
-- to transport (the state contributes nothing to a restricted context) —
-- and the `St₁`-weakening is one generic conjugation step on top.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- UTILITIES
------------------------------------------------------------------------

-- A lock-freeness witness is unique.

Lock-free-irr : ∀ {Δ} → (p q : Lock-free Δ) → p ≡ q
Lock-free-irr lf-[]     lf-[]      = refl
Lock-free-irr (lf-∷ p)  (lf-∷ q)   = cong lf-∷ (Lock-free-irr p q)

-- A renaming out of a provably empty context acts like any transport.

empty-src-≐ : ∀ {Γ₀ Γ₁} → (e₀ : Γ₀ ≡ []) → (r : Ren [] Γ₀ Γ₁)
            → (e : Γ₀ ≡ Γ₁) → r ≐ʳ eq-ren e
empty-src-≐ e₀ r e =
  mk≐ʳ (λ x → ⊥-elim (not-in-empty-ctx
                       (subst (λ Γ₂ → _ ∈[ _ ] Γ₂) e₀ x)))

-- The eternal-values action at a provably empty prefix is a transport.

env-eternal-C-empty : ∀ {Δ₀ Γc C} → (e : Δ₀ ≡ [])
                    → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                    → (M : (Δ₀ ++ᶜ Γc) ⊢C⦂ C)
                    → env-eternal-C lf η M
                    ≡ castᶜ (trans (cong (_++ᶜ Γc) e) (++ᶜ-identityˡ {Γc})) M
env-eternal-C-empty {Γc = Γc} e lf-[] η M =
  castᶜ-irr (++ᶜ-identityˡ {Γc}) (trans (cong (_++ᶜ Γc) e) (++ᶜ-identityˡ {Γc})) M
env-eternal-C-empty e (lf-∷ lf) η M with e
... | ()

-- The eternal-values action respects a transport of its suffix.

env-eternal-C-suffix : ∀ {Δ₀ Γc Γc' C} → (e : Γc ≡ Γc')
                     → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                     → (M : (Δ₀ ++ᶜ Γc) ⊢C⦂ C)
                     → castᶜ e (env-eternal-C lf η M)
                     ≡ env-eternal-C lf η (castᶜ (cong (Δ₀ ++ᶜ_) e) M)
env-eternal-C-suffix refl lf η M = refl

-- Fusing a conjugation whose core is itself an `eq-ren`.

conj-eq-≐ : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'}
          → {R : Ren [] Γ₁ Γ₂'} → (e : Γ₁ ≡ Γ₁') → (e₀ : Γ₁' ≡ Γ₂)
          → (e' : Γ₂ ≡ Γ₂')
          → R ≐ʳconj⟨ e , eq-ren e₀ , e' ⟩
          → R ≐ʳ eq-ren (trans e (trans e₀ e'))
conj-eq-≐ e e₀ e' h =
  ≐ʳ-trans h
    (≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (eq-ren-∘-≐ e e₀))
              (≐ʳ-trans (eq-ren-∘-≐ (trans e e₀) e')
                        (eq-ren-≐ _ _)))

-- A loop of four casts is the identity.

cast-loop₄ : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃)
           → (e₃ : Γ₃ ≡ Γ₄) → (e₄ : Γ₄ ≡ Γ₁) → (M : Γ₁ ⊢C⦂ C)
           → castᶜ e₄ (castᶜ e₃ (castᶜ e₂ (castᶜ e₁ M))) ≡ M
cast-loop₄ refl refl refl e₄ M = castᶜ-irr e₄ refl M

-- A loop of two casts is the identity.

cast-loop₂ : ∀ {Γ₁ Γ₂ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₁) → (M : Γ₁ ⊢C⦂ C)
           → castᶜ e₂ (castᶜ e₁ M) ≡ M
cast-loop₂ refl e₂ M = castᶜ-irr e₂ refl M

-- A chain of two casts is one transport.

cast-chain₂ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃)
            → (M : Γ₁ ⊢C⦂ C)
            → castᶜ e₂ (castᶜ e₁ M) ≡ subst (_⊢C⦂ C) (trans e₁ e₂) M
cast-chain₂ refl refl M = refl

-- A chain of four casts is one transport.

cast-chain₄ : ∀ {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃)
            → (e₃ : Γ₃ ≡ Γ₄) → (e₄ : Γ₄ ≡ Γ₅) → (M : Γ₁ ⊢C⦂ C)
            → castᶜ e₄ (castᶜ e₃ (castᶜ e₂ (castᶜ e₁ M)))
            ≡ subst (_⊢C⦂ C) (trans e₁ (trans e₂ (trans e₃ e₄))) M
cast-chain₄ refl refl refl refl M = refl

------------------------------------------------------------------------
-- THE STATE-FREE CORE
--
-- `env-Hˢ γ Δ K` is `env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)` of the
-- clause, up to transport: the state's part of the restricted context is
-- empty, so every state-indexed zone of `env-Hˢ` contributes only a
-- transport, and the value-substituting zones match `env-eternal-C`'s
-- own steps.
------------------------------------------------------------------------

-- The recursion's suffix context.

D~ : Ctx → VType → Op → E → Ctx
D~ Δ B op ε =
  Δ ᴱ ∷ type-of-gtype (param op)
      ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε)

eStar : ∀ {B} → (St : 𝕊 []) → (Δ : Ctx) → (op : Op) → (ε : E)
      → ([] ++ᶜ D~ Δ B op ε)
      ≡ ((toCtx St ++ᶜ Δ) ᴱ ∷ type-of-gtype (param op)
           ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B ‼ ε))
eStar {B} St Δ op ε =
  trans (++ᶜ-identityˡ {D~ Δ B op ε})
        (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (toCtxᴱ-++ᶜ St Δ)))

-- The eternal-values action respects the equivalence (the computation
-- counterpart of `env-eternal-V-≐`).

env-eternal-C-≐ : ∀ {Δ Γ C} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                → {M M' : (Δ ++ᶜ Γ) ⊢C⦂ C} → M ≐ᶜ M'
                → env-eternal-C lf η M ≐ᶜ env-eternal-C lf η M'
env-eternal-C-≐ lf-[]                 η eM = castᶜ-≐ ++ᶜ-identityˡ eM
env-eternal-C-≐ {Δ ∷ B} {Γ} (lf-∷ lf) η eM =
  env-eternal-C-≐ lf (λ x → η (Tl-∷ x))
    (castᶜ-≐ _ (sub-≐ᶜ (split→∈ (split-≡-++ᶜ {Δ ∷ B} {Γ})) (≐ᵛ-refl _) eM))

------------------------------------------------------------------------
-- ONE SUBSTITUTION PAST THE ETERNAL CHAIN
--
-- `env-eternal-C` peels its prefix from the *right*, while `env-Hˢ`
-- reaches a zone's substitution only after the zones to its left have
-- run. So the two open cases both need to move one substitution past the
-- whole chain. Each step of the chain substitutes the entry immediately
-- to the left of the one being moved — `Δ ∷ B` against `([] ∷ A) ++ᶜ Θ'`
-- *is* `(Δ ∷ B ∷ A) ++ᶜ Θ'` — so each step is exactly one `sub-swap-C`.
--
-- Note `env-eternal-C (lf-∷ lf) η` *is* `env-eternal-C lf η' ∘ sub-atᶜ`,
-- definitionally: the two agree on the nose, which is what makes the
-- induction below readable.
------------------------------------------------------------------------

env-eternal-C-swap : ∀ {Δ₀ A C} → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                   → (Θ' : Ctx) → (V : [] ⊢V⦂ A)
                   → (M : ((Δ₀ ∷ A) ++ᶜ Θ') ⊢C⦂ C)
                   → castᶜ (++ᶜ-identityˡ {Θ'})
                       (sub-atᶜ {[]} {A} Θ'
                         (env-eternal-C lf η
                           (castᶜ (++ᶜ-assoc Δ₀ ([] ∷ A) Θ') M)) V)
                   ≐ᶜ env-eternal-C lf η
                        (sub-atᶜ {Δ₀} {A} Θ' M (V-rename (empty-ren lf) V))

env-eternal-C-swap {Δ₀} {A} {C} lf-[] η Θ' V M =
  ≐ᶜ-trans
    (castᶜ-≐ (++ᶜ-identityˡ {Θ'})
      (sub-atᶜ-≐ {[]} {A} Θ' V
        (≡→≐ᶜ (cast-loop₂ (++ᶜ-assoc [] ([] ∷ A) Θ') (++ᶜ-identityˡ) M))))
    (castᶜ-≐ (++ᶜ-identityˡ {Θ'})
      (sub-atᶜ-≐ᵥ {[]} {A} Θ' M (≐ᵛ-sym (V-rename-id-≐ ≐ʳ-refl V))))

env-eternal-C-swap {Δ ∷ B} {A} {C} (lf-∷ lf) η Θ' V M =
  ≐ᶜ-trans
    (≡→≐ᶜ (cong (λ z → castᶜ (++ᶜ-identityˡ {Θ'})
                         (sub-atᶜ {[]} {A} Θ' (env-eternal-C lf η' z) V))
                (sym (cast-loop₂ (sym (++ᶜ-assoc Δ ([] ∷ A) Θ'))
                                 (++ᶜ-assoc Δ ([] ∷ A) Θ')
                                 (sub-atᶜ {Δ} {B} (([] ∷ A) ++ᶜ Θ')
                                    (castᶜ (++ᶜ-assoc (Δ ∷ B) ([] ∷ A) Θ') M)
                                    W₁)))))
    (≐ᶜ-trans (env-eternal-C-swap lf η' Θ' V (inner₀ᶜ Θ' M W₁))
      (env-eternal-C-≐ lf η'
        (≐ᶜ-trans (≐ᶜ-sym (sub-swap-C Θ' M W₂ W₁))
                  (sub-atᶜ-≐ {Δ} {B} Θ' W₁
                    (sub-atᶜ-≐ᵥ {Δ ∷ B} {A} Θ' M
                      (≐ᵛ-sym (V-rename-∘ (wk-ren {A = B})
                                          (empty-ren lf) V)))))))
  where
    η' : ClosedVals Δ
    η' x = η (Tl-∷ x)

    W₁ = V-rename (empty-ren lf) (η Hd)
    W₂ = V-rename (empty-ren lf) V

------------------------------------------------------------------------
-- THE CHAIN AT A CONCATENATED PREFIX
--
-- At `eternalˡ` the mismatch is block for block: `env-Hˢ` runs the
-- eternal zone's substitutions before the zones to its left, while
-- `env-eternal-C` at `Δ₁ ++ᶜ Δ₂` peels `Δ₂` first. Splitting the
-- concatenated chain one entry at a time reduces that to
-- `env-eternal-C-swap`: each entry of `Δ₂` moves past the whole of `Δ₁`,
-- and the entry left over is adjacent to the chain it crosses.
------------------------------------------------------------------------

-- The values of a concatenated prefix. By recursion on `Δ₂`'s
-- lock-freeness, so that peeling an entry is definitional.

++ᶜᵛ : ∀ {Δ₁ Δ₂} → Lock-free Δ₂ → ClosedVals Δ₁ → ClosedVals Δ₂
     → ClosedVals (Δ₁ ++ᶜ Δ₂)
++ᶜᵛ lf-[]      η₁ η₂ x        = η₁ x
++ᶜᵛ (lf-∷ lf₂) η₁ η₂ Hd       = η₂ Hd
++ᶜᵛ (lf-∷ lf₂) η₁ η₂ (Tl-∷ x) = ++ᶜᵛ lf₂ η₁ (λ y → η₂ (Tl-∷ y)) x

-- and the same values, presented against the splitting `env-ᴱ` dispatches
-- on rather than by recursion

splitVal : ∀ {Δ₁ Δ₂ A ρ} → ClosedVals Δ₁ → ClosedVals Δ₂
         → (Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ₁) ⊎ (A ∈[ ρ ] Δ₂) → [] ⊢V⦂ A
splitVal η₁ η₂ (inj₁ (_ , y)) = η₁ y
splitVal η₁ η₂ (inj₂ y)       = η₂ y

++ᶜᵛ-split : ∀ {Δ₁ Δ₂ A ρ} → (lf₂ : Lock-free Δ₂)
           → (η₁ : ClosedVals Δ₁) → (η₂ : ClosedVals Δ₂)
           → (y : A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂))
           → ++ᶜᵛ lf₂ η₁ η₂ y ≡ splitVal η₁ η₂ (∈-++ᶜ-split Δ₁ Δ₂ y)
++ᶜᵛ-split lf-[]      η₁ η₂ y  = refl
++ᶜᵛ-split (lf-∷ lf₂) η₁ η₂ Hd = refl
++ᶜᵛ-split {Δ₁} {Δ₂ ∷ B} (lf-∷ lf₂) η₁ η₂ (Tl-∷ y)
  with ∈-++ᶜ-split Δ₁ Δ₂ y | ++ᶜᵛ-split lf₂ η₁ (λ z → η₂ (Tl-∷ z)) y
... | inj₁ p | q = q
... | inj₂ z | q = q

-- The chain uses its values only pointwise.

env-eternal-C-η : ∀ {Δ Θ C} → (lf : Lock-free Δ) → {η η' : ClosedVals Δ}
                → (∀ {A ρ} → (x : A ∈[ ρ ] Δ) → η x ≡ η' x)
                → (M : (Δ ++ᶜ Θ) ⊢C⦂ C)
                → env-eternal-C lf η M ≡ env-eternal-C lf η' M
env-eternal-C-η lf-[] h M = refl
env-eternal-C-η {Δ ∷ B} {Θ} (lf-∷ lf) {η} {η'} h M =
  trans (cong (λ z → env-eternal-C lf (λ x → η (Tl-∷ x))
                       (sub-atᶜ {Δ} {B} Θ M (V-rename (empty-ren lf) z)))
              (h Hd))
        (env-eternal-C-η lf (λ x → h (Tl-∷ x))
          (sub-atᶜ {Δ} {B} Θ M (V-rename (empty-ren lf) (η' Hd))))

-- and it respects a transport of its prefix.

env-eternal-C-pre : ∀ {Δ Δ' Θ C} → (e : Δ ≡ Δ')
                  → (lf : Lock-free Δ) → (lf' : Lock-free Δ')
                  → (η : ClosedVals Δ) → (η' : ClosedVals Δ')
                  → (∀ {A ρ} → (x : A ∈[ ρ ] Δ)
                       → η x ≡ η' (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x))
                  → (M : (Δ ++ᶜ Θ) ⊢C⦂ C)
                  → env-eternal-C lf η M
                  ≡ env-eternal-C lf' η' (castᶜ (cong (_++ᶜ Θ) e) M)
env-eternal-C-pre refl lf lf' η η' h M
  rewrite Lock-free-irr lf lf' = env-eternal-C-η lf' h M

-- The decomposition itself.

env-eternal-C-++ : ∀ {Δ₁ Δ₂ Θ C} → (lf₁ : Lock-free Δ₁) → (lf₂ : Lock-free Δ₂)
                 → (lf₁₂ : Lock-free (Δ₁ ++ᶜ Δ₂))
                 → (η₁ : ClosedVals Δ₁) → (η₂ : ClosedVals Δ₂)
                 → (M : ((Δ₁ ++ᶜ Δ₂) ++ᶜ Θ) ⊢C⦂ C)
                 → env-eternal-C lf₁₂ (++ᶜᵛ lf₂ η₁ η₂) M
                 ≐ᶜ env-eternal-C lf₂ η₂
                      (env-eternal-C lf₁ η₁ (castᶜ (++ᶜ-assoc Δ₁ Δ₂ Θ) M))

env-eternal-C-++ {Δ₁} {[]} {Θ} lf₁ lf-[] lf₁₂ η₁ η₂ M =
  ≐ᶜ-trans (≡→≐ᶜ (env-eternal-C-pre refl lf₁₂ lf₁ _ η₁ (λ x → refl) M))
    (≡→≐ᶜ (sym
      (trans (env-eternal-C-suffix (++ᶜ-identityˡ {Θ}) lf₁ η₁ _)
             (cong (env-eternal-C lf₁ η₁)
                   (cast-loop₂ (++ᶜ-assoc Δ₁ [] Θ)
                               (cong (Δ₁ ++ᶜ_) (++ᶜ-identityˡ {Θ})) M)))))

env-eternal-C-++ {Δ₁} {Δ₂ ∷ B} {Θ} {C} lf₁ (lf-∷ lf₂) (lf-∷ lf₁₂) η₁ η₂ M =
  ≐ᶜ-trans (≐ᶜ-sym (env-eternal-C-swap lf₁₂ (++ᶜᵛ lf₂ η₁ η₂') Θ (η₂ Hd) M))
    (≐ᶜ-trans
      (castᶜ-≐ (++ᶜ-identityˡ {Θ})
        (sub-atᶜ-≐ {[]} {B} Θ (η₂ Hd)
          (≐ᶜ-trans (env-eternal-C-++ lf₁ lf₂ lf₁₂ η₁ η₂' (castᶜ c₂ M))
                    (env-eternal-C-≐ lf₂ η₂' (≡→≐ᶜ qeq)))))
      (env-eternal-C-swap lf₂ η₂' Θ (η₂ Hd) M̃))
  where
    η₂' : ClosedVals Δ₂
    η₂' x = η₂ (Tl-∷ x)

    c₂ = ++ᶜ-assoc (Δ₁ ++ᶜ Δ₂) ([] ∷ B) Θ
    c₁ = ++ᶜ-assoc Δ₁ Δ₂ (([] ∷ B) ++ᶜ Θ)
    c₃ = ++ᶜ-assoc Δ₁ (Δ₂ ∷ B) Θ

    M̃ = env-eternal-C lf₁ η₁ (castᶜ c₃ M)

    qeq : env-eternal-C lf₁ η₁ (castᶜ c₁ (castᶜ c₂ M))
        ≡ castᶜ (++ᶜ-assoc Δ₂ ([] ∷ B) Θ) M̃
    qeq =
      trans
        (cong (env-eternal-C lf₁ η₁)
          (trans (cast-chain₂ c₂ c₁ M)
            (trans (cong (λ p → subst (_⊢C⦂ C) p M) uip)
                   (sym (cast-chain₂ c₃
                          (cong (Δ₁ ++ᶜ_) (++ᶜ-assoc Δ₂ ([] ∷ B) Θ)) M)))))
        (sym (env-eternal-C-suffix (++ᶜ-assoc Δ₂ ([] ∷ B) Θ) lf₁ η₁
                                   (castᶜ c₃ M)))

------------------------------------------------------------------------
-- THE ETERNAL ZONE'S CLAUSE ACTION IS A CHAIN
--
-- `env-eternal-H` peels `Δ₀` itself; `env-eternal-C` peels the *restricted*
-- `Δ₀ ᴱ`. At a non-eternal entry the first is a transport and the second
-- has nothing to peel; at an eternal one both substitute the restricted
-- value, and in the same order — so, unlike `eternalˡ` as a whole, this
-- needs no swap, only the per-entry dispatch.
------------------------------------------------------------------------

-- Restricting a closed value is the identity: it has no variables to move.

restrict-closed : ∀ {A} → (et : Eternal A) → (V : [] ⊢V⦂ A)
                → eternal-val-restrict et V ≡ V
restrict-closed (Baseₑ b p)    (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed (Baseₑ b p)    (const c)   = refl
restrict-closed Unitₑ          (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed Unitₑ          ⋆           = refl
restrict-closed Emptyₑ         (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed (et₁ |×|ₑ et₂) (var f x)   = ⊥-elim (not-in-empty-ctx x)
restrict-closed (et₁ |×|ₑ et₂) ⦉ V₁ , V₂ ⦊ =
  cong₂ (λ U₁ U₂ → ⦉ U₁ , U₂ ⦊)
        (restrict-closed et₁ V₁) (restrict-closed et₂ V₂)

-- An eternal zone's values, on the context the chain peels.

ηᴱ : ∀ {Δ₀} → ClosedVals Δ₀ → ClosedVals (Δ₀ ᴱ)
ηᴱ {Δ₀} η y = η (proj₂ (∈-ᴱ⁻ Δ₀ y))

-- The clause context, split at the zone's own boundary.

eH : (Δ₀ Γc : Ctx) → (B : VType) → (op : Op) → (ε : E)
   → ((Δ₀ ++ᶜ Γc) ᴱ ++ᶜ Dcl B op ε)
   ≡ (Δ₀ ᴱ ++ᶜ (Γc ᴱ ++ᶜ Dcl B op ε))
eH Δ₀ Γc B op ε =
  trans (cong (_++ᶜ Dcl B op ε) (ᴱ-++ᶜ Δ₀ Γc))
        (++ᶜ-assoc (Δ₀ ᴱ) (Γc ᴱ) (Dcl B op ε))

-- As `env-Hˢ-ᴱ-∷`, except that here the decision can be taken *before*
-- the statement is made: every occurrence of `eternal? B₀` sits under one
-- of the rollout's `Dec`-taking forms, so the entry is stated at `d` and
-- matched directly — no `rewrite`, hence no with-abstraction to reorder.

env-eternal-H-C-∷ : ∀ {B₀ Δ Γc B} → (lf : Lock-free Δ)
                  → (η : ClosedVals (Δ ∷ B₀))
                  → (K : Fam B (((Δ ∷ B₀) ++ᶜ Γc) ᴱ)) → (op : Op) → (ε : E)
                  → (d : Dec (Eternal B₀))
                  → (e₁ : (((Δ ∷ B₀) ++ᶜ Γc) ᴱ ++ᶜ Dcl B op ε)
                        ≡ (ᴱ-∷ (Δ ᴱ) B₀ d ++ᶜ (Γc ᴱ ++ᶜ Dcl B op ε)))
                  → (ih : (K₀ : Fam B ((Δ ++ᶜ Γc) ᴱ))
                        → env-eternal-H {_} {Γc} lf (λ x → η (Tl-∷ x)) K₀ op ε
                        ≐ᶜ env-eternal-C {_} {Γc ᴱ ++ᶜ Dcl B op ε}
                             (ᴱ-lock-free Δ) (ηᴱ (λ x → η (Tl-∷ x)))
                             (castᶜ (eH Δ Γc B op ε) (K₀ op ε)))
                  → env-eternal-H {_} {Γc} lf (λ x → η (Tl-∷ x))
                       (sub-atᴴ′ d Γc K (V-rename (empty-ren lf) (η Hd))) op ε
                  ≐ᶜ env-eternal-C {_} {Γc ᴱ ++ᶜ Dcl B op ε}
                       (ᴱ-lock-free-∷ Δ B₀ d)
                       (λ y → η (proj₂ (∈-ᴱ⁻-∷ Δ B₀ d y)))
                       (castᶜ e₁ (K op ε))

env-eternal-H-C : ∀ {Δ₀ Γc B} → (lf : Lock-free Δ₀) → (η : ClosedVals Δ₀)
                → (K : Fam B ((Δ₀ ++ᶜ Γc) ᴱ)) → (op : Op) → (ε : E)
                → env-eternal-H {_} {Γc} lf η K op ε
                ≐ᶜ env-eternal-C {_} {Γc ᴱ ++ᶜ Dcl B op ε}
                     (ᴱ-lock-free Δ₀) (ηᴱ η)
                     (castᶜ (eH Δ₀ Γc B op ε) (K op ε))

env-eternal-H-C {[]} {Γc} {B} lf-[] η K op ε =
  ≐ᶜ-sym (≡→≐ᶜ
    (trans (cast-chain₂ (eH [] Γc B op ε)
                        (++ᶜ-identityˡ {Γc ᴱ ++ᶜ Dcl B op ε}) (K op ε))
      (trans (cong (λ p → subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) p (K op ε)) uip)
             (sym (castᶜ≡subst
                     (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                                     ∷ [ mapᵉ (op-grade op) ]
                                         (type-of-gtype (arity op) ⇒ B ‼ ε))
                           (++ᶜ-identityˡ {Γc}))
                     (K op ε))))))

env-eternal-H-C {Δ ∷ B₀} {Γc} {B} (lf-∷ lf) η K op ε =
  env-eternal-H-C-∷ lf η K op ε (eternal? B₀) (eH (Δ ∷ B₀) Γc B op ε)
    (λ K₀ → env-eternal-H-C lf (λ x → η (Tl-∷ x)) K₀ op ε)

-- at a non-eternal entry neither side peels: the clause substitution is a
-- transport and the entry is absent from the restricted prefix

env-eternal-H-C-∷ {B₀} {Δ} {Γc} {B} lf η K op ε (no ¬et) e₁ ih =
  ≐ᶜ-trans (ih K₄) (≡→≐ᶜ (cong (env-eternal-C (ᴱ-lock-free Δ) (ηᴱ η')) inner))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε

    η' : ClosedVals Δ
    η' x = η (Tl-∷ x)

    W₀ = V-rename (empty-ren lf) (η Hd)

    K₄ : Fam B ((Δ ++ᶜ Γc) ᴱ)
    K₄ = sub-atᴴ′ (no ¬et) Γc K W₀

    cCl = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (castOf {Δ} {B₀} Γc)

    dropM = ᴱ-drop-split ¬et (bvar {Δ} B₀ Γc)

    inner : castᶜ (eH Δ Γc B op ε) (K₄ op ε) ≡ castᶜ e₁ (K op ε)
    inner =
      trans (cong (λ z → castᶜ (eH Δ Γc B op ε) (castᶜ cCl z))
                  (subst-++ᶜʳ Dc dropM (K op ε)))
        (trans (cong (castᶜ (eH Δ Γc B op ε))
                  (trans (castᶜ≡subst cCl _)
                         (subst-fuseᶜ (cong (_++ᶜ Dc) dropM) cCl (K op ε))))
          (trans (castᶜ≡subst (eH Δ Γc B op ε) _)
            (trans (subst-fuseᶜ (trans (cong (_++ᶜ Dc) dropM) cCl)
                                (eH Δ Γc B op ε) (K op ε))
              (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
                     (sym (castᶜ≡subst e₁ (K op ε)))))))

-- at an eternal one both sides substitute the restricted value, and both
-- do it first, so `cl-yes` and `sub-at-≐` align them where they stand

env-eternal-H-C-∷ {B₀} {Δ} {Γc} {B} lf η K op ε (yes et) e₁ ih =
  ≐ᶜ-trans (ih K₄)
    (env-eternal-C-≐ (ᴱ-lock-free Δ) (ηᴱ η')
      (isSub-≐ (isSub-reassoc isL isMid) (isSub-refl S₂) (≐ᶜ-sym swapStep)))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε
    Θᴱ = Γc ᴱ ++ᶜ Dc

    η' : ClosedVals Δ
    η' x = η (Tl-∷ x)

    W₀ = V-rename (empty-ren lf) (η Hd)

    K₄ : Fam B ((Δ ++ᶜ Γc) ᴱ)
    K₄ = sub-atᴴ′ (yes et) Γc K W₀

    x  = bvar {Δ} B₀ Γc
    Wv = bval {Δ} {B₀} Γc W₀

    sl = split→∈-split-l (split-≡-++ᶜ {Δ ∷ B₀} {Γc})
    sr = split→∈-split-r (split-≡-++ᶜ {Δ ∷ B₀} {Γc})

    V₂ = V-rename (empty-ren (ᴱ-lock-free Δ)) (η Hd)

    eclx = eCl et x B op ε

    X₁ = subst (_⊢C⦂ CT) eclx (K op ε)
    X₂ = castᶜ e₁ (K op ε)

    eΓ : split-l x ᴱ ≡ Δ ᴱ
    eΓ = cong _ᴱ sl

    eΘ : (split-r x ᴱ ++ᶜ Dc) ≡ Θᴱ
    eΘ = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ Dc) sr

    e  = cong₂ (λ Γ₁ Θ₁ → (Γ₁ ∷ B₀) ++ᶜ Θ₁) eΓ eΘ
    e' = cong₂ _++ᶜ_ eΓ eΘ

    -- both are transports of the same clause
    mid : X₂ ≐ᶜ subst (_⊢C⦂ CT) e X₁
    mid =
      ≡→≐ᶜ (trans (castᶜ≡subst e₁ (K op ε))
             (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
                    (sym (subst-fuseᶜ eclx e (K op ε)))))

    eVal : subst (_⊢V⦂ B₀) eΓ (eternal-val-restrict et Wv) ≐ᵛ V₂
    eVal =
      ≐ᵛ-trans
        (≡→≐ᵛ
          (trans (cong (λ z → subst (_⊢V⦂ B₀) eΓ (eternal-val-restrict et z))
                       (castᵛ≡subst (sym sl) W₀))
            (trans (cong (subst (_⊢V⦂ B₀) eΓ)
                         (restrict-substᵛ (sym sl) et W₀))
              (trans (subst-fuseᵛ (cong _ᴱ (sym sl)) eΓ
                                  (eternal-val-restrict et W₀))
                     (substᵛ-irr (trans (cong _ᴱ (sym sl)) eΓ) refl
                                 (eternal-val-restrict et W₀))))))
        (≐ᵛ-trans (eternal-val-restrict-ren et (empty-ren lf) (η Hd))
          (≐ᵛ-trans
            (≡→≐ᵛ (cong (V-rename (restrict-ren (empty-ren lf)))
                        (restrict-closed et (η Hd))))
            (V-rename-≐ (∅-ren-≐ (restrict-ren (empty-ren lf))
                                     (empty-ren (ᴱ-lock-free Δ)))
                        (η Hd))))

    S₁ = sub-atᶜ {split-l x ᴱ} {B₀} (split-r x ᴱ ++ᶜ Dc) X₁
                 (eternal-val-restrict et Wv)

    S₂ = sub-atᶜ {Δ ᴱ} {B₀} Θᴱ X₂ V₂

    swapStep : S₂ ≐ᶜ subst (_⊢C⦂ CT) e' S₁
    swapStep =
      sub-at-≐ eΓ eΘ X₁ X₂ e mid (eternal-val-restrict et Wv) V₂ eVal e'

    isL = isSub-cast _ (eH Δ Γc B op ε)
            (isSub-Cl op ε _ (castOf {Δ} {B₀} Γc)
              (cl-yes et x Wv K op ε eclx))

    isMid : IsSub S₁ (subst (_⊢C⦂ CT) e' S₁)
    isMid = e' , refl

-- THE TELESCOPE ENTRY
--
-- The clause is split off, taking the eternality decision *and* the
-- equation naming it, plus its own induction hypothesis (as
-- `ren-sub-unbox` does). That is the only way in: a bare `with eternal? A`
-- on the `_∷ᵉ_` clause hoists the decision ahead of `St`, `Γ`, `γ`, `W`,
-- `Δ`, `K` and leaves an occurrence un-abstracted, because the statement
-- mentions fixed proof terms whose types mention `(Γ ∷ A) ᴱ`. Here every
-- variable is already fixed, so `rewrite` touches the goal alone.

env-Hˢ-ᴱ-∷ : ∀ {St Γ A B} → (γ : Env St Γ) → (W : toCtx St ⊢V⦂ A)
           → (Δ : Ctx) → (K : Fam B (((Γ ∷ A) ++ᶜ Δ) ᴱ))
           → (op : Op) → (ε : E)
           → (e₁ : (((Γ ∷ A) ++ᶜ Δ) ᴱ ++ᶜ Dcl B op ε)
                 ≡ ((Γ ∷ A) ᴱ ++ᶜ ([] ++ᶜ D~ Δ B op ε)))
           → (d : Dec (Eternal A)) → eternal? A ≡ d
           → (ih : (Δ₀ : Ctx) → (K₀ : Fam B ((Γ ++ᶜ Δ₀) ᴱ))
                 → env-Hˢ γ Δ₀ K₀ op ε
                 ≐ᶜ castᶜ (eStar St Δ₀ op ε)
                      (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
                        (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ₀ B op ε))
                          (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ₀) (K₀ op ε)))))
           → env-Hˢ (γ ∷ᵉ W) Δ K op ε
           ≐ᶜ castᶜ (eStar St Δ op ε)
                (env-eternal-C (ᴱ-lock-free (Γ ∷ A)) (env-ᴱ (γ ∷ᵉ W))
                  (castᶜ e₁ (K op ε)))

env-Hˢ-ᴱ : ∀ {St Γ B} → (γ : Env St Γ) → (Δ : Ctx)
         → (K : Fam B ((Γ ++ᶜ Δ) ᴱ)) → (op : Op) → (ε : E)
         → env-Hˢ γ Δ K op ε
         ≐ᶜ castᶜ (eStar St Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
               (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ) (K op ε))))

-- the state contributes nothing: the prefix is provably empty and every
-- transport loops back to the clause itself

env-Hˢ-ᴱ {B = B} ⌊ St ⌋ Δ K op ε =
  ≐ᶜ-sym (≡→≐ᶜ
    (trans (cong (castᶜ (eStar St Δ op ε))
                 (env-eternal-C-empty (toCtxᴱ-[] St)
                                      (ᴱ-lock-free (toCtx St)) _ _))
           (cast-loop₄
              (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε))
                    (ᴱ-++ᶜ (toCtx St) Δ))
              (++ᶜ-assoc (toCtx St ᴱ) [] (D~ Δ B op ε))
              (trans (cong (_++ᶜ ([] ++ᶜ D~ Δ B op ε)) (toCtxᴱ-[] St))
                     (++ᶜ-identityˡ {[] ++ᶜ D~ Δ B op ε}))
              (eStar St Δ op ε) (K op ε))))
-- the base weakening restricts to a transport ([] has no variables)

env-Hˢ-ᴱ {B = B} (∅ᵉ St) Δ K op ε =
  ≐ᶜ-trans
    (C-rename-eq-≐ (cong (_++ᶜ Dcl B op ε) Efull) hren (K op ε))
    (≡→≐ᶜ (sym rhs-eq))
  where
    Efull = trans (ᴱ-++ᶜ [] Δ)
                  (trans (cong (_++ᶜ Δ ᴱ) (sym (toCtxᴱ-[] St)))
                         (sym (ᴱ-++ᶜ (toCtx St) Δ)))

    hren : cong-∷-ren (cong-∷-ren
             (restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (∅-ren St))))
         ≐ʳ eq-ren (cong (_++ᶜ Dcl B op ε) Efull)
    hren =
      ≐ʳ-trans (cong-ren-≐ (Dcl B op ε) inner)
               (cong-ren-eq-ren-≐ (Dcl B op ε) Efull)
      where
        inner : restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (∅-ren St))
              ≐ʳ eq-ren Efull
        inner =
          conj-eq-≐ (ᴱ-++ᶜ [] Δ)
                    (cong (_++ᶜ Δ ᴱ) (sym (toCtxᴱ-[] St)))
                    (sym (ᴱ-++ᶜ (toCtx St) Δ))
            (≐ʳ-trans
              (restrict-cong-≐ (∅-ren St) Δ (ᴱ-++ᶜ [] Δ)
                                            (ᴱ-++ᶜ (toCtx St) Δ))
              (∘ʳ-≐ ≐ʳ-refl
                (∘ʳ-≐ (≐ʳ-trans
                         (cong-ren-≐ (Δ ᴱ)
                           (∅-ren-≐ _ (eq-ren (sym (toCtxᴱ-[] St)))))
                         (cong-ren-eq-ren-≐ (Δ ᴱ) (sym (toCtxᴱ-[] St))))
                      ≐ʳ-refl)))

    rhs-eq : castᶜ (eStar St Δ op ε)
               (castᶜ (++ᶜ-identityˡ {[] ++ᶜ D~ Δ B op ε})
                 (castᶜ (++ᶜ-assoc ([] ᴱ) [] (D~ Δ B op ε))
                   (castᶜ (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op)
                                                ⇒ B ‼ ε))
                                (ᴱ-++ᶜ [] Δ))
                          (K op ε))))
           ≡ subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε))
                   (cong (_++ᶜ Dcl B op ε) Efull) (K op ε)
    rhs-eq =
      trans (cast-chain₄
               (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                               ∷ [ mapᵉ (op-grade op) ]
                                   (type-of-gtype (arity op) ⇒ B ‼ ε))
                     (ᴱ-++ᶜ [] Δ))
               (++ᶜ-assoc ([] ᴱ) [] (D~ Δ B op ε))
               (++ᶜ-identityˡ {[] ++ᶜ D~ Δ B op ε})
               (eStar St Δ op ε) (K op ε))
            (cong (λ p → subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) p (K op ε)) uip)
-- a slice's restriction is a transport between provably-empty state parts

env-Hˢ-ᴱ {B = B} (sliceᵉ {St} {St'} γ q) Δ K op ε =
  ≐ᶜ-trans (C-rename-eq-≐ Ewhole hren (env-Hˢ γ Δ K op ε))
    (≐ᶜ-trans (substᶜ-≐ Ewhole (env-Hˢ-ᴱ γ Δ K op ε))
      (≡→≐ᶜ (trans (cong (subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) Ewhole)
                         (castᶜ≡subst (eStar St Δ op ε) _))
              (trans (subst-fuseᶜ (eStar St Δ op ε) Ewhole _)
                (trans (cong (λ p → subst (_⊢C⦂ B ‼ (op-grade op ·ₑ ε)) p _)
                             (uip {p = trans (eStar St Δ op ε) Ewhole}
                                  {q = eStar St' Δ op ε}))
                       (sym (castᶜ≡subst (eStar St' Δ op ε) _)))))))
  where
    EStSt' = trans (toCtxᴱ-[] St) (sym (toCtxᴱ-[] St'))

    Einner = trans (ᴱ-++ᶜ (toCtx St) Δ)
                   (trans (cong (_++ᶜ Δ ᴱ) EStSt')
                          (sym (ᴱ-++ᶜ (toCtx St') Δ)))

    Ewhole = cong (_++ᶜ Dcl B op ε) Einner

    hren : cong-∷-ren (cong-∷-ren
             (restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (slice-renᵘ q))))
         ≐ʳ eq-ren Ewhole
    hren =
      ≐ʳ-trans (cong-ren-≐ (Dcl B op ε) inner)
               (cong-ren-eq-ren-≐ (Dcl B op ε) Einner)
      where
        inner : restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (slice-renᵘ q))
              ≐ʳ eq-ren Einner
        inner =
          conj-eq-≐ (ᴱ-++ᶜ (toCtx St) Δ) (cong (_++ᶜ Δ ᴱ) EStSt')
                    (sym (ᴱ-++ᶜ (toCtx St') Δ))
            (≐ʳ-trans
              (restrict-cong-≐ (slice-renᵘ q) Δ (ᴱ-++ᶜ (toCtx St) Δ)
                                                (ᴱ-++ᶜ (toCtx St') Δ))
              (∘ʳ-≐ ≐ʳ-refl
                (∘ʳ-≐ (≐ʳ-trans
                         (cong-ren-≐ (Δ ᴱ)
                           (empty-src-≐ (toCtxᴱ-[] St) _ EStSt'))
                         (cong-ren-eq-ren-≐ (Δ ᴱ) EStSt'))
                      ≐ʳ-refl)))
-- a lock: the recursion at the lock-absorbing suffix; the crossing
-- renaming restricts to a transport, and the suffix relocation moves
-- inside `env-eternal-C`

env-Hˢ-ᴱ {B = B} (_⟨_⟩ᵉ {St} {St'} {Γ} {ρ} γ q) Δ K op ε =
  ≐ᶜ-trans (C-rename-eq-≐ EW hren _)
    (≐ᶜ-trans
      (substᶜ-≐ EW (castᶜ-≐ eo (env-Hˢ-ᴱ γ Δ' K' op ε)))
      (≡→≐ᶜ step))
  where
    CT = B ‼ (op-grade op ·ₑ ε)

    Δ' = [] ⟨ ρ ⟩ ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ) (K op' ε')

    eo = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ ⟩) Δ))

    E₁₂ = trans (toCtxᴱ-[] St) (sym (toCtxᴱ-[] St'))

    EI = trans (ᴱ-++ᶜ (toCtx St ⟨ ρ ⟩) Δ)
               (trans (cong (_++ᶜ Δ ᴱ) E₁₂)
                      (sym (ᴱ-++ᶜ (toCtx St') Δ)))

    EW = cong (_++ᶜ Dcl B op ε) EI

    hren : cong-∷-ren (cong-∷-ren
             (restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (unbox-ren q))))
         ≐ʳ eq-ren EW
    hren =
      ≐ʳ-trans (cong-ren-≐ (Dcl B op ε) inner)
               (cong-ren-eq-ren-≐ (Dcl B op ε) EI)
      where
        inner : restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} (unbox-ren q))
              ≐ʳ eq-ren EI
        inner =
          conj-eq-≐ (ᴱ-++ᶜ (toCtx St ⟨ ρ ⟩) Δ) (cong (_++ᶜ Δ ᴱ) E₁₂)
                    (sym (ᴱ-++ᶜ (toCtx St') Δ))
            (≐ʳ-trans
              (restrict-cong-≐ (unbox-ren q) Δ (ᴱ-++ᶜ (toCtx St ⟨ ρ ⟩) Δ)
                                               (ᴱ-++ᶜ (toCtx St') Δ))
              (∘ʳ-≐ ≐ʳ-refl
                (∘ʳ-≐ (≐ʳ-trans
                         (cong-ren-≐ (Δ ᴱ)
                           (empty-src-≐ (toCtxᴱ-[] St) _ E₁₂))
                         (cong-ren-eq-ren-≐ (Δ ᴱ) E₁₂))
                      ≐ʳ-refl)))

    eΔ'Δ : Δ' ᴱ ≡ Δ ᴱ
    eΔ'Δ = trans (ᴱ-++ᶜ ([] ⟨ ρ ⟩) Δ) (++ᶜ-identityˡ {Δ ᴱ})

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ ([] ++ᶜ D~ Δ B op ε)
    eSuf = cong (λ Γ₁ → [] ++ᶜ (Γ₁ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε)))
                eΔ'Δ

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ⟨ ρ ⟩) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    cE = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (ᴱ-++ᶜ (Γ ⟨ ρ ⟩) Δ)

    X' = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
             (castᶜ cE' (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
               (sym (cast-chain₂ cE (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                                 (K op ε))))

    step : subst (_⊢C⦂ CT) EW
             (castᶜ eo (castᶜ (eStar St Δ' op ε) X'))
         ≡ castᶜ (eStar St' Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
               (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))))
    step =
      trans (cong (subst (_⊢C⦂ CT) EW)
                  (cast-chain₂ (eStar St Δ' op ε) eo X'))
        (trans (subst-fuseᶜ (trans (eStar St Δ' op ε) eo) EW X')
          (trans (cong (λ p → subst (_⊢C⦂ CT) p X') uip)
            (trans (sym (cast-chain₂ eSuf (eStar St' Δ op ε) X'))
              (cong (castᶜ (eStar St' Δ op ε))
                (trans (env-eternal-C-suffix eSuf (ᴱ-lock-free Γ)
                                             (env-ᴱ γ) _)
                       (cong (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ))
                             inner-eq))))))
-- a telescope entry, and the eternal prefix. Both are open; see the note
-- below `env-eternal-C-swap` and `notes/adequacy-plan.md` for what they
-- need and why `with eternal? A` is not the way in.

env-Hˢ-ᴱ {B = B} (_∷ᵉ_ {St} {Γ} {A} γ W) Δ K op ε =
  ≐ᶜ-trans
    (env-Hˢ-ᴱ-∷ γ W Δ K op ε
       (trans (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε))
                    (ᴱ-++ᶜ (Γ ∷ A) Δ))
              (++ᶜ-assoc ((Γ ∷ A) ᴱ) [] (D~ Δ B op ε)))
       (eternal? A) refl (λ Δ₀ K₀ → env-Hˢ-ᴱ γ Δ₀ K₀ op ε))
    (≡→≐ᶜ (cong (λ z → castᶜ (eStar St Δ op ε)
                         (env-eternal-C (ᴱ-lock-free (Γ ∷ A))
                                        (env-ᴱ (γ ∷ᵉ W)) z))
                (trans (castᶜ≡subst _ (K op ε))
                  (sym (cast-chain₂
                          (cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                                          ∷ [ mapᵉ (op-grade op) ]
                                              (type-of-gtype (arity op)
                                                ⇒ B ‼ ε))
                                (ᴱ-++ᶜ (Γ ∷ A) Δ))
                          (++ᶜ-assoc ((Γ ∷ A) ᴱ) [] (D~ Δ B op ε))
                          (K op ε))))))

env-Hˢ-ᴱ {B = B} (liftᵉ {St} {Γ} {A} {ρ} V γ) Δ K op ε =
  ≐ᶜ-trans (castᶜ-≐ eo (env-Hˢ-ᴱ γ Δ' K' op ε)) (≡→≐ᶜ step)
  where
    CT = B ‼ (op-grade op ·ₑ ε)

    Δ' = [] ∷ [ ρ ] A ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ) (K op' ε')

    eo = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ ] A) Δ))

    eΔ'Δ : Δ' ᴱ ≡ Δ ᴱ
    eΔ'Δ = trans (ᴱ-++ᶜ ([] ∷ [ ρ ] A) Δ) (++ᶜ-identityˡ {Δ ᴱ})

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ ([] ++ᶜ D~ Δ B op ε)
    eSuf = cong (λ Γ₁ → [] ++ᶜ (Γ₁ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε)))
                eΔ'Δ

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ∷ [ ρ ] A) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    cE = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (ᴱ-++ᶜ (Γ ∷ [ ρ ] A) Δ)

    X' = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
             (castᶜ cE' (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
               (sym (cast-chain₂ cE (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                                 (K op ε))))

    step : castᶜ eo (castᶜ (eStar St Δ' op ε) X')
         ≡ castᶜ (eStar (St ∷ₛ V) Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
               (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
                 (castᶜ cE (K op ε))))
    step =
      trans (cast-chain₂ (eStar St Δ' op ε) eo X')
        (trans (cong (λ p → subst (_⊢C⦂ CT) p X') uip)
          (trans (sym (cast-chain₂ eSuf (eStar (St ∷ₛ V) Δ op ε) X'))
            (cong (castᶜ (eStar (St ∷ₛ V) Δ op ε))
              (trans (env-eternal-C-suffix eSuf (ᴱ-lock-free Γ)
                                           (env-ᴱ γ) _)
                     (cong (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ))
                           inner-eq)))))
-- an eternal zone: `env-Hˢ` runs it before the zones to its left, the
-- restriction peels it last. `env-eternal-H-C` turns the zone's clause
-- action into a chain at `Δ₀ ᴱ`, and `env-eternal-C-++` splits the
-- restriction's own chain at `Δ₀ ᴱ ++ᶜ Γ ᴱ` into the same two halves.

env-Hˢ-ᴱ {St} {B = B} (eternalˡ {Γ = Γ} Δ₀ lf η γ) Δ K op ε =
  ≐ᶜ-trans (env-Hˢ-ᴱ γ Δ K₂ op ε)
    (castᶜ-≐ (eStar St Δ op ε)
      (≐ᶜ-trans
        (env-eternal-C-≐ (ᴱ-lock-free Γ) (env-ᴱ γ)
          (≐ᶜ-trans
            (castᶜ-≐ a₁ (castᶜ-≐ cR (env-eternal-H-C lf η K₃ op ε)))
            (≡→≐ᶜ midEq)))
        (≐ᶜ-trans
          (≐ᶜ-sym (env-eternal-C-++ (ᴱ-lock-free Δ₀) (ᴱ-lock-free Γ)
                     lf₁₂ (ηᴱ η) (env-ᴱ γ) M₀))
          (≡→≐ᶜ preEq))))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Θ  = [] ++ᶜ D~ Δ B op ε
    Γ₊ = Γ ++ᶜ Δ

    K₃ : Fam B ((Δ₀ ++ᶜ Γ₊) ᴱ)
    K₃ op' ε' = Cl-cast op' ε' (++ᶜ-assoc Δ₀ Γ Δ) (K op' ε')

    K₂ : Fam B ((Γ ++ᶜ Δ) ᴱ)
    K₂ = env-eternal-H {Δ₀} {Γ₊} lf η K₃

    a₁ = ++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε)

    cR = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (ᴱ-++ᶜ Γ Δ)

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Δ₀ Γ Δ)

    cRᴿ = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ (Δ₀ ++ᶜ Γ) Δ)

    lf₁₂ : Lock-free (Δ₀ ᴱ ++ᶜ Γ ᴱ)
    lf₁₂ = subst Lock-free (ᴱ-++ᶜ Δ₀ Γ) (ᴱ-lock-free (Δ₀ ++ᶜ Γ))

    Y₀ = castᶜ (++ᶜ-assoc ((Δ₀ ++ᶜ Γ) ᴱ) [] (D~ Δ B op ε))
           (castᶜ cRᴿ (K op ε))

    M₀ = castᶜ (cong (_++ᶜ Θ) (ᴱ-++ᶜ Δ₀ Γ)) Y₀

    -- the two casts between the halves move inside the inner chain, and
    -- both towers are transports of the same clause
    midEq : castᶜ a₁
              (castᶜ cR
                (env-eternal-C {_} {Γ₊ ᴱ ++ᶜ Dcl B op ε}
                   (ᴱ-lock-free Δ₀) (ηᴱ η)
                   (castᶜ (eH Δ₀ Γ₊ B op ε) (K₃ op ε))))
          ≡ env-eternal-C (ᴱ-lock-free Δ₀) (ηᴱ η)
              (castᶜ (++ᶜ-assoc (Δ₀ ᴱ) (Γ ᴱ) Θ) M₀)
    midEq =
      trans (cong (castᶜ a₁)
               (env-eternal-C-suffix cR (ᴱ-lock-free Δ₀) (ηᴱ η) _))
        (trans (env-eternal-C-suffix a₁ (ᴱ-lock-free Δ₀) (ηᴱ η) _)
          (cong (env-eternal-C (ᴱ-lock-free Δ₀) (ηᴱ η))
            (trans (cast-chain₄ cKassoc (eH Δ₀ Γ₊ B op ε)
                      (cong (Δ₀ ᴱ ++ᶜ_) cR) (cong (Δ₀ ᴱ ++ᶜ_) a₁) (K op ε))
              (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
                     (sym (cast-chain₄ cRᴿ
                             (++ᶜ-assoc ((Δ₀ ++ᶜ Γ) ᴱ) [] (D~ Δ B op ε))
                             (cong (_++ᶜ Θ) (ᴱ-++ᶜ Δ₀ Γ))
                             (++ᶜ-assoc (Δ₀ ᴱ) (Γ ᴱ) Θ) (K op ε)))))))

    -- `env-ᴱ` at an eternal zone *is* the concatenated values
    hη : ∀ {A ρ} → (x : A ∈[ ρ ] ((Δ₀ ++ᶜ Γ) ᴱ))
       → env-ᴱ (eternalˡ Δ₀ lf η γ) x
       ≡ splitVal (ηᴱ η) (env-ᴱ γ)
           (∈-++ᶜ-split (Δ₀ ᴱ) (Γ ᴱ)
             (subst (λ Γ₁ → _ ∈[ _ ] Γ₁) (ᴱ-++ᶜ Δ₀ Γ) x))
    hη x
      with ∈-++ᶜ-split (Δ₀ ᴱ) (Γ ᴱ)
             (subst (λ Γ₁ → _ ∈[ _ ] Γ₁) (ᴱ-++ᶜ Δ₀ Γ) x)
    ... | inj₁ (ρ' , y) = refl
    ... | inj₂ y        = refl

    hpre : ∀ {A ρ} → (y : A ∈[ ρ ] (Δ₀ ᴱ ++ᶜ Γ ᴱ))
         → ++ᶜᵛ (ᴱ-lock-free Γ) (ηᴱ η) (env-ᴱ γ) y
         ≡ env-ᴱ (eternalˡ Δ₀ lf η γ)
             (subst (λ Γ₁ → A ∈[ ρ ] Γ₁) (sym (ᴱ-++ᶜ Δ₀ Γ)) y)
    hpre y =
      trans (++ᶜᵛ-split (ᴱ-lock-free Γ) (ηᴱ η) (env-ᴱ γ) y)
        (sym (trans (hη (subst (λ Γ₁ → _ ∈[ _ ] Γ₁) (sym (ᴱ-++ᶜ Δ₀ Γ)) y))
               (cong (λ z → splitVal (ηᴱ η) (env-ᴱ γ)
                              (∈-++ᶜ-split (Δ₀ ᴱ) (Γ ᴱ) z))
                     (subst-subst-sym′ (ᴱ-++ᶜ Δ₀ Γ) y))))

    preEq : env-eternal-C lf₁₂ (++ᶜᵛ (ᴱ-lock-free Γ) (ηᴱ η) (env-ᴱ γ)) M₀
          ≡ env-eternal-C (ᴱ-lock-free (Δ₀ ++ᶜ Γ))
              (env-ᴱ (eternalˡ Δ₀ lf η γ)) Y₀
    preEq =
      trans (env-eternal-C-pre (sym (ᴱ-++ᶜ Δ₀ Γ)) lf₁₂
               (ᴱ-lock-free (Δ₀ ++ᶜ Γ)) _ (env-ᴱ (eternalˡ Δ₀ lf η γ))
               hpre M₀)
            (cong (env-eternal-C (ᴱ-lock-free (Δ₀ ++ᶜ Γ))
                                 (env-ᴱ (eternalˡ Δ₀ lf η γ)))
                  (cast-loop₂ (cong (_++ᶜ Θ) (ᴱ-++ᶜ Δ₀ Γ))
                              (cong (_++ᶜ Θ) (sym (ᴱ-++ᶜ Δ₀ Γ))) Y₀))

------------------------------------------------------------------------
-- THE ASSEMBLY: `env-Hˢ-clause` FROM THE STATE-FREE CORE
--
-- The outer weakening decomposes onto `cong-ren {Δ ᴱ ∷ p ∷ k} (∅-ren St₁)`
-- — exactly the renaming `env-Cˢ (env-clause γ St₁)` applies — and the
-- leftover transports loop.
------------------------------------------------------------------------

env-Hˢ-clause : ∀ {St Γ B} → (γ : Env St Γ) → (St₁ : 𝕊 []) → (Δ : Ctx)
               → (K : Fam B ((Γ ++ᶜ Δ) ᴱ)) → (op : Op) → (ε : E)
               → C-rename (cong-∷-ren (cong-∷-ren
                             (clause-ren St₁ Δ ∘ʳ eq-ren (toCtxᴱ-++ᶜ St Δ))))
                          (env-Hˢ γ Δ K op ε)
               ≐ᶜ env-Cˢ (env-clause γ St₁)
                         (Δ ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B ‼ ε))
                         (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ) (K op ε))

env-Hˢ-clause {St} {Γ} {B} γ St₁ Δ K op ε =
  ≐ᶜ-trans
    (C-rename-cong _ (env-Hˢ-ᴱ γ Δ K op ε))
    (≐ᶜ-trans
      (C-rename-conj eIn eOut hconj
         (castᶜ (eStar St Δ op ε) X))
      (≡→≐ᶜ
        (trans (cong (subst (_⊢C⦂ CT) eOut)
                 (cong (C-rename (cong-ren {Γ'' = D~ Δ B op ε} (∅-ren St₁)))
                   (trans (cong (subst (_⊢C⦂ CT) eIn)
                                (castᶜ≡subst (eStar St Δ op ε) X))
                     (trans (subst-fuseᶜ (eStar St Δ op ε) eIn X)
                            (subst-loopᶜ _ X)))))
               (subst-loopᶜ eOut _))))
  where
    CT = B ‼ (op-grade op ·ₑ ε)

    X = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
          (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ B op ε))
            (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ) (K op ε)))

    eIn : ((toCtx St ++ᶜ Δ) ᴱ ∷ type-of-gtype (param op)
             ∷ [ mapᵉ (op-grade op) ]
                 (type-of-gtype (arity op) ⇒ B ‼ ε))
        ≡ ([] ++ᶜ D~ Δ B op ε)
    eIn = sym (eStar St Δ op ε)

    eOut : (toCtx St₁ ++ᶜ D~ Δ B op ε)
         ≡ (toCtx St₁ ++ᶜ D~ Δ B op ε)
    eOut = refl

    hconj : cong-∷-ren (cong-∷-ren
              (clause-ren St₁ Δ ∘ʳ eq-ren (toCtxᴱ-++ᶜ St Δ)))
          ≐ʳconj⟨ eIn , cong-ren {Γ'' = D~ Δ B op ε} (∅-ren St₁) , eOut ⟩
    hconj =
      ≐ʳ-trans
        (conj-cong-ren (Dcl B op ε) EA refl
          (≐ʳ-trans
            (≐ʳ-trans (∘ʳ-≐ hsplit ≐ʳ-refl) (∘ʳ-assoc-≐ _ _ _))
            (≐ʳ-trans
              (≐ʳ-sym (∘ʳ-identityˡ-≐ _))
              (∘ʳ-≐ (eq-ren-≐ refl refl)
                (∘ʳ-≐ ≐ʳ-refl (eq-ren-∘-≐ (toCtxᴱ-++ᶜ St Δ)
                                          (sym (++ᶜ-identityˡ {Δ ᴱ}))))))))
        (≐ʳ-trans
          (conj-fuse (cong (_++ᶜ Dcl B op ε) EA) refl
             (++ᶜ-assoc [] (Δ ᴱ) (Dcl B op ε))
             (sym (++ᶜ-assoc (toCtx St₁) (Δ ᴱ) (Dcl B op ε)))
             (cong-ren-assoc-≐ (Δ ᴱ) (Dcl B op ε) (∅-ren St₁)))
          (∘ʳ-≐ (eq-ren-≐ _ eOut) (∘ʳ-≐ ≐ʳ-refl (eq-ren-≐ _ eIn))))
      where
        EA = trans (toCtxᴱ-++ᶜ St Δ) (sym (++ᶜ-identityˡ {Δ ᴱ}))

        hsplit : clause-ren St₁ Δ
               ≐ʳ (cong-ren {Γ'' = Δ ᴱ} (∅-ren St₁)
                   ∘ʳ eq-ren (sym (++ᶜ-identityˡ {Δ ᴱ})))
        hsplit = ≐ʳ-refl

-- at a non-eternal entry the whole zone disappears from both sides: the
-- clause substitution is a transport and so is the entry's contribution
-- to the restriction, so this is `liftᵉ`'s case with one transport more

env-Hˢ-ᴱ-∷ {St} {Γ} {A} {B} γ W Δ K op ε e₁ (no ¬et) eq ih rewrite eq =
  ≐ᶜ-trans
    (castᶜ-≐ cOut
      (substᶜ-≐′ (λ Γ₀ → Γ₀ ++ᶜ Dc) dropM
        (castᶜ-≐ eo (ih Δ' K'))))
    (≡→≐ᶜ step)
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε

    Δ' = [] ∷ A ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ A) Δ) (K op' ε')

    cOut = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B ‼ ε))
                (castOf {toCtx St} {A} Δ)

    dropM = ᴱ-drop-split ¬et (bvar {toCtx St} A Δ)

    eo = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))

    -- `A` is not eternal, so it drops out of the restricted suffix
    eΔ'Δ : Δ' ᴱ ≡ Δ ᴱ
    eΔ'Δ = trans (ᴱ-++ᶜ ([] ∷ A) Δ)
             (trans (cong (_++ᶜ Δ ᴱ) (ᴱ-∷-drop {[]} {A} ¬et))
                    (++ᶜ-identityˡ {Δ ᴱ}))

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ ([] ++ᶜ D~ Δ B op ε)
    eSuf = cong (λ Γ₁ → [] ++ᶜ (Γ₁ ∷ type-of-gtype (param op)
                                  ∷ [ mapᵉ (op-grade op) ]
                                      (type-of-gtype (arity op) ⇒ B ‼ ε)))
                eΔ'Δ

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ∷ A) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    X' = env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
             (castᶜ cE' (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ e₁ (K op ε)
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ p → subst (_⊢C⦂ CT) p (K op ε)) uip)
               (sym (castᶜ≡subst e₁ (K op ε))))

    step : castᶜ cOut
             (subst (λ Γ₀ → (Γ₀ ++ᶜ Dc) ⊢C⦂ CT) dropM
               (castᶜ eo (castᶜ (eStar St Δ' op ε) X')))
         ≡ castᶜ (eStar St Δ op ε)
             (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ) (castᶜ e₁ (K op ε)))
    step =
      trans (cong (λ z → castᶜ cOut
                           (subst (λ Γ₀ → (Γ₀ ++ᶜ Dc) ⊢C⦂ CT) dropM z))
                  (cast-chain₂ (eStar St Δ' op ε) eo X'))
        (trans (cong (castᶜ cOut) (subst-++ᶜʳ Dc dropM _))
          (trans (castᶜ≡subst cOut _)
            (trans (subst-fuseᶜ (cong (_++ᶜ Dc) dropM) cOut
                     (subst (_⊢C⦂ CT) (trans (eStar St Δ' op ε) eo) X'))
              (trans (subst-fuseᶜ (trans (eStar St Δ' op ε) eo)
                                  (trans (cong (_++ᶜ Dc) dropM) cOut) X')
                (trans (cong (λ p → subst (_⊢C⦂ CT) p X') uip)
                  (trans (sym (cast-chain₂ eSuf (eStar St Δ op ε) X'))
                    (cong (castᶜ (eStar St Δ op ε))
                      (trans (env-eternal-C-suffix eSuf (ᴱ-lock-free Γ)
                                                   (env-ᴱ γ) _)
                             (cong (env-eternal-C (ᴱ-lock-free Γ) (env-ᴱ γ))
                                   inner-eq)))))))))
-- at an eternal entry both sides substitute the restricted value, but at
-- different prefixes: the clause zone at the state's (provably empty)
-- one, `env-eternal-C` at `Γ ᴱ`, and only after the chain to its left.
-- `cl-yes` presents the former as a `sub-atᶜ`, `sub-at-≐` aligns the two,
-- and `env-eternal-C-swap` moves the latter past the chain.

env-Hˢ-ᴱ-∷ {St} {Γ} {A} {B} γ W Δ K op ε e₁ (yes et) eq ih rewrite eq =
  ≐ᶜ-trans lhs-step
    (castᶜ-≐ (eStar St Δ op ε)
      (env-eternal-C-swap lf (env-ᴱ γ) Θ' V₂ (castᶜ e₁ (K op ε))))
  where
    CT = B ‼ (op-grade op ·ₑ ε)
    Dc = Dcl B op ε
    lf = ᴱ-lock-free Γ

    Θ' = [] ++ᶜ D~ Δ B op ε
    Δ' = [] ∷ A ++ᶜ Δ

    K' : Fam B ((Γ ++ᶜ Δ') ᴱ)
    K' op' ε' = Cl-cast op' ε' (++ᶜ-assoc Γ ([] ∷ A) Δ) (K op' ε')

    Krec : Fam B (((toCtx St ∷ A) ++ᶜ Δ) ᴱ)
    Krec op' ε' = Cl-cast op' ε' (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
                    (env-Hˢ γ Δ' K' op' ε')

    x  = bvar {toCtx St} A Δ
    Wv = bval {toCtx St} {A} Δ W

    sl = split→∈-split-l (split-≡-++ᶜ {toCtx St ∷ A} {Δ})
    sr = split→∈-split-r (split-≡-++ᶜ {toCtx St ∷ A} {Δ})

    V₂ = castᵛ (toCtxᴱ-[] St) (eternal-val-restrict et W)

    eclx = eCl et x B op ε

    X₁ = subst (_⊢C⦂ CT) eclx (Krec op ε)

    X₂ = env-eternal-C lf (env-ᴱ γ)
           (castᶜ (++ᶜ-assoc (Γ ᴱ) ([] ∷ A) Θ') (castᶜ e₁ (K op ε)))

    -- the state's half of the splitting is empty, the other half is `Δ`
    eΓ : split-l x ᴱ ≡ []
    eΓ = trans (cong _ᴱ sl) (toCtxᴱ-[] St)

    eΘ : (split-r x ᴱ ++ᶜ Dc) ≡ Θ'
    eΘ = trans (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ Dc) sr)
               (sym (++ᶜ-identityˡ {D~ Δ B op ε}))

    e  = cong₂ (λ Γ₁ Θ₁ → (Γ₁ ∷ A) ++ᶜ Θ₁) eΓ eΘ
    e' = cong₂ _++ᶜ_ eΓ eΘ

    -- `A` is eternal, so it survives into the recursion's restricted suffix
    eΔsuf : ([] ++ᶜ Δ' ᴱ) ≡ (([] ∷ A) ++ᶜ ([] ++ᶜ Δ ᴱ))
    eΔsuf = trans (++ᶜ-identityˡ {Δ' ᴱ})
              (trans (ᴱ-++ᶜ ([] ∷ A) Δ)
                (trans (cong (_++ᶜ Δ ᴱ) (ᴱ-∷-keep {[]} {A} et))
                       (cong (([] ∷ A) ++ᶜ_) (sym (++ᶜ-identityˡ {Δ ᴱ})))))

    eSuf : ([] ++ᶜ D~ Δ' B op ε) ≡ (([] ∷ A) ++ᶜ Θ')
    eSuf = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B ‼ ε))
                eΔsuf

    cAssoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                            ∷ [ mapᵉ (op-grade op) ]
                                (type-of-gtype (arity op) ⇒ B ‼ ε))
                  (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))

    cKassoc = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε))
                   (++ᶜ-assoc Γ ([] ∷ A) Δ)

    cE' = cong (λ Γ₁ → Γ₁ ∷ type-of-gtype (param op)
                         ∷ [ mapᵉ (op-grade op) ]
                             (type-of-gtype (arity op) ⇒ B ‼ ε))
               (ᴱ-++ᶜ Γ Δ')

    Y = env-eternal-C lf (env-ᴱ γ)
          (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
            (Cl-castᴿ op ε (ᴱ-++ᶜ Γ Δ') (K' op ε)))

    inner-eq : castᶜ (cong (Γ ᴱ ++ᶜ_) eSuf)
                 (castᶜ (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
                   (castᶜ cE' (castᶜ cKassoc (K op ε))))
             ≡ castᶜ (++ᶜ-assoc (Γ ᴱ) ([] ∷ A) Θ') (castᶜ e₁ (K op ε))
    inner-eq =
      trans (cast-chain₄ cKassoc cE'
               (++ᶜ-assoc (Γ ᴱ) [] (D~ Δ' B op ε))
               (cong (Γ ᴱ ++ᶜ_) eSuf) (K op ε))
        (trans (cong (λ q → subst (_⊢C⦂ CT) q (K op ε)) uip)
               (sym (cast-chain₂ e₁ (++ᶜ-assoc (Γ ᴱ) ([] ∷ A) Θ') (K op ε))))

    collapse : subst (_⊢C⦂ CT) e
                 (subst (_⊢C⦂ CT) eclx
                   (castᶜ cAssoc (castᶜ (eStar St Δ' op ε) Y)))
             ≡ X₂
    collapse =
      trans (cong (λ z → subst (_⊢C⦂ CT) e (subst (_⊢C⦂ CT) eclx z))
                  (cast-chain₂ (eStar St Δ' op ε) cAssoc Y))
        (trans (cong (subst (_⊢C⦂ CT) e)
                     (subst-fuseᶜ (trans (eStar St Δ' op ε) cAssoc) eclx Y))
          (trans (subst-fuseᶜ (trans (trans (eStar St Δ' op ε) cAssoc) eclx) e Y)
            (trans (cong (λ q → subst (_⊢C⦂ CT) q Y) uip)
              (trans (sym (castᶜ≡subst eSuf Y))
                (trans (env-eternal-C-suffix eSuf lf (env-ᴱ γ) _)
                       (cong (env-eternal-C lf (env-ᴱ γ)) inner-eq))))))

    mid : X₂ ≐ᶜ subst (_⊢C⦂ CT) e X₁
    mid =
      ≐ᶜ-sym
        (≐ᶜ-trans (substᶜ-≐ e (substᶜ-≐ eclx (castᶜ-≐ cAssoc (ih Δ' K'))))
                  (≡→≐ᶜ collapse))

    eVal : subst (_⊢V⦂ A) eΓ (eternal-val-restrict et Wv) ≐ᵛ V₂
    eVal =
      ≡→≐ᵛ
        (trans (cong (λ z → subst (_⊢V⦂ A) eΓ (eternal-val-restrict et z))
                     (castᵛ≡subst (sym sl) W))
          (trans (cong (subst (_⊢V⦂ A) eΓ) (restrict-substᵛ (sym sl) et W))
            (trans (subst-fuseᵛ (cong _ᴱ (sym sl)) eΓ
                                (eternal-val-restrict et W))
              (trans (substᵛ-irr _ (toCtxᴱ-[] St) (eternal-val-restrict et W))
                     (sym (castᵛ≡subst (toCtxᴱ-[] St)
                                       (eternal-val-restrict et W)))))))

    S₁ = sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dc) X₁
                 (eternal-val-restrict et Wv)

    S₂ = sub-atᶜ {[]} {A} Θ' X₂ V₂

    swapStep : S₂ ≐ᶜ subst (_⊢C⦂ CT) e' S₁
    swapStep =
      sub-at-≐ eΓ eΘ X₁ X₂ e mid (eternal-val-restrict et Wv) V₂ eVal e'

    isL = isSub-Cl op ε _ (castOf {toCtx St} {A} Δ)
            (cl-yes et x Wv Krec op ε eclx)

    isMid : IsSub S₁ (subst (_⊢C⦂ CT) e' S₁)
    isMid = e' , refl

    isR = isSub-cast _ (eStar St Δ op ε)
            (isSub-cast _ (++ᶜ-identityˡ {Θ'}) (isSub-refl S₂))

    lhs-step = isSub-≐ (isSub-reassoc isL isMid) isR (≐ᶜ-sym swapStep)

------------------------------------------------------------------------
-- THE ACTION ON THE CELL AN `unbox` NAMES
--
-- Reduction consults an `unbox` only through its cell (`unbox-tgt`), and that
-- is also all `_≐ᶜ_` compares, so this is what the action does to an `unbox`.
-- The zones that rename move the cell by `var-tgt′`; the zones that substitute
-- move it by `⟨_⟩[_↦_]rvar`, the value put in a resource variable's place
-- being of box type and hence itself a variable.
--
-- Only the cell is tracked, not its grade bound: `unbox-var-≐` does not see the
-- bound, so every consumer recovers whichever bound it needs from the term.
------------------------------------------------------------------------

-- one step of the eternal zone's chain

env-eternal-cell : ∀ {Δ Γc A ρ} → Lock-free Δ → ClosedVals Δ
                 → Tgt (Δ ++ᶜ Γc) ([ ρ ] A) → Tgt Γc ([ ρ ] A)

env-eternal-cell lf-[] η t = Tgt-cast ++ᶜ-identityˡ t

env-eternal-cell {Δ ∷ B} {Γc} (lf-∷ lf) η (σ , z) =
  env-eternal-cell lf (λ x → η (Tl-∷ x))
    (Tgt-cast (castOf {Δ} {B} Γc)
      (proj₁ (⟨ z ⟩[ bvar B Γc ↦ bval Γc (V-rename (empty-ren lf) (η Hd)) ]rvar)
      , proj₁ (proj₂ (⟨ z ⟩[ bvar B Γc
                             ↦ bval Γc (V-rename (empty-ren lf) (η Hd)) ]rvar))))

env-cell : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
         → Tgt (Γ ++ᶜ Δ) ([ ρ ] A) → Tgt (toCtx St ++ᶜ Δ) ([ ρ ] A)

env-cell ⌊ St ⌋      Δ t = t
env-cell (∅ᵉ St)     Δ t = var-tgt′ (cong-ren (∅-ren St)) t
env-cell (sliceᵉ γ q) Δ t =
  var-tgt′ (cong-ren (slice-renᵘ q)) (env-cell γ Δ t)

env-cell (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ t =
  var-tgt′ (cong-ren (unbox-ren q))
    (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ))
      (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
        (Tgt-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t =
  Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ))
    (env-cell γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
      (Tgt-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t))

env-cell (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ t =
  Tgt-cast (castOf {toCtx St} {A₀} Δ)
    (proj₁ (⟨ z ⟩[ bvar A₀ Δ ↦ bval Δ W ]rvar)
    , proj₁ (proj₂ (⟨ z ⟩[ bvar A₀ Δ ↦ bval Δ W ]rvar)))
  where
    z = proj₂ (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ))
                 (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                   (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

env-cell (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ t =
  env-cell γ Δ
    (env-eternal-cell lf η (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ) t))

-- The readability bound travels with the cell. Renaming a variable can only
-- lower its grade (`var-rename`'s own bound, discharged at a box type, which is
-- never eternal), and `⟨_⟩[_↦_]rvar` carries its bound as its third component —
-- so a cell readable at `ρ` stays readable at `ρ` wherever the action puts it.

var-tgt-≾ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ Γ')
          → (x : [ ρ ] A ∈[ σ ] Γ) → proj₁ (var-tgt r x) ≾ᵣ σ
var-tgt-≾ r x = proj₁ (proj₂ (var-rename r x)) (λ ())

env-eternal-cell-rel : ∀ {Δ Γc A ρ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                     → (t : Tgt (Δ ++ᶜ Γc) ([ ρ ] A))
                     → proj₁ t ≾ᵣ ρ
                     → proj₁ (env-eternal-cell lf η t) ≾ᵣ ρ

env-eternal-cell-rel lf-[] η t rel = rel

env-eternal-cell-rel {Δ ∷ B} {Γc} (lf-∷ lf) η (σ , z) rel =
  env-eternal-cell-rel lf (λ x → η (Tl-∷ x)) _
    (≾ᵣ-trans
      (proj₂ (proj₂ (⟨ z ⟩[ bvar B Γc
                            ↦ bval Γc (V-rename (empty-ren lf) (η Hd)) ]rvar)))
      rel)

env-cell-rel : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → (t : Tgt (Γ ++ᶜ Δ) ([ ρ ] A))
             → proj₁ t ≾ᵣ ρ
             → proj₁ (env-cell γ Δ t) ≾ᵣ ρ

env-cell-rel ⌊ St ⌋       Δ t rel = rel
env-cell-rel (∅ᵉ St)      Δ t rel =
  ≾ᵣ-trans (var-tgt-≾ (cong-ren (∅-ren St)) (proj₂ t)) rel
env-cell-rel (sliceᵉ γ q) Δ t rel =
  ≾ᵣ-trans (var-tgt-≾ (cong-ren (slice-renᵘ q)) (proj₂ (env-cell γ Δ t)))
           (env-cell-rel γ Δ t rel)

env-cell-rel (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ t rel =
  ≾ᵣ-trans (var-tgt-≾ (cong-ren (unbox-ren q)) z)
           (env-cell-rel γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                         (Tgt-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t) rel)
  where
    z = proj₂ (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ))
                 (env-cell γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                   (Tgt-cast (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) t)))

env-cell-rel (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ t rel =
  env-cell-rel γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
               (Tgt-cast (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) t) rel

env-cell-rel (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ t rel =
  ≾ᵣ-trans
    (proj₂ (proj₂ (⟨ z ⟩[ bvar A₀ Δ ↦ bval Δ W ]rvar)))
    (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ) (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t) rel)
  where
    z = proj₂ (Tgt-cast (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ))
                 (env-cell γ ([] ∷ A₀ ++ᶜ Δ)
                   (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) t)))

env-cell-rel (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ t rel =
  env-cell-rel γ Δ _
    (env-eternal-cell-rel lf η (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ) t) rel)

-- and the same on computations, zone for zone

env-Cˢ-≐ : ∀ {St Γ C} → (γ : Env St Γ) → (Δ : Ctx) → {M M' : (Γ ++ᶜ Δ) ⊢C⦂ C}
         → M ≐ᶜ M' → env-Cˢ γ Δ M ≐ᶜ env-Cˢ γ Δ M'

env-Cˢ-≐ ⌊ St ⌋       Δ eM = eM
env-Cˢ-≐ (∅ᵉ St)      Δ eM = C-rename-cong _ eM
env-Cˢ-≐ (sliceᵉ γ q) Δ eM = C-rename-cong _ (env-Cˢ-≐ γ Δ eM)
env-Cˢ-≐ (γ ⟨ q ⟩ᵉ)   Δ eM =
  C-rename-cong _ (castᶜ-≐ _ (env-Cˢ-≐ γ _ (castᶜ-≐ _ eM)))
env-Cˢ-≐ (liftᵉ V γ)  Δ eM = castᶜ-≐ _ (env-Cˢ-≐ γ _ (castᶜ-≐ _ eM))
env-Cˢ-≐ (_∷ᵉ_ {St = St} {Γ = Γ} {A = A} γ W) Δ eM =
  castᶜ-≐ (cong₂ _++ᶜ_ (split→∈-split-l t) (split→∈-split-r t))
    (sub-≐ᶜ (split→∈ t) (≐ᵛ-refl (castᵛ (sym (split→∈-split-l t)) W))
      (castᶜ-≐ (sym (++ᶜ-assoc (toCtx St) ([] ∷ A) Δ))
        (env-Cˢ-≐ γ ([] ∷ A ++ᶜ Δ) (castᶜ-≐ (++ᶜ-assoc Γ ([] ∷ A) Δ) eM))))
  where
    t = split-≡-++ᶜ {toCtx St ∷ A} {Δ}
env-Cˢ-≐ (eternalˡ Δ₀ lf η γ) Δ eM =
  env-Cˢ-≐ γ Δ (env-eternal-C-≐ lf η (castᶜ-≐ _ eM))

------------------------------------------------------------------------
-- THE ACTION COMMUTES WITH `unbox`
--
-- The action sends an `unbox` to an `unbox` at the cell `env-cell` computes.
-- Only up to `_≐ᶜ_`, and necessarily so: the renaming zones compose their
-- renaming into the one the node stores, while the substituting zones
-- renormalise the node entirely (`unbox⇒var` then `unbox-var`), so the stored
-- renaming and boxed value do not agree on the nose — which is exactly why
-- `unbox-≐` compares the cell alone.
------------------------------------------------------------------------

-- Recognising a node by its cell.

unbox-cell-≐ : ∀ {Γ A C ρ Δ₀ σ} → {w : Ren [] (Δ₀ ⟨ ρ ⟩) Γ} → {V : Δ₀ ⊢V⦂ [ ρ ] A}
             → {z : [ ρ ] A ∈[ σ ] Γ} → (rel : σ ≾ᵣ ρ)
             → unbox-tgt w V ≡ (σ , z)
             → {N N' : Γ ∷ A ⊢C⦂ C} → N ≐ᶜ N'
             → unbox w V N ≐ᶜ unbox-var z rel N'
unbox-cell-≐ rel eq eN = unbox-≐ (trans eq (sym (unbox-var-tgt _ rel))) eN

-- and moving a recognised node along a transport of its context

unbox-var-cast-≐ : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ') → (t : Tgt Γ ([ ρ ] A))
                 → (rel rel' : proj₁ t ≾ᵣ ρ)
                 → (N : Γ ∷ A ⊢C⦂ C)
                 → castᶜ e (unbox-var (proj₂ t) rel N)
                 ≐ᶜ unbox-var (proj₂ (Tgt-cast e t)) rel'
                              (castᶜ (cong (_∷ A) e) N)
unbox-var-cast-≐ refl t rel rel' N = unbox-var-≐ (proj₂ t) rel rel' (≐ᶜ-refl N)

------------------------------------------------------------------------
-- THE ACTION COMMUTES WITH `unbox`
--
-- The action sends an `unbox` to an `unbox` at the cell `env-cell` computes.
-- Only up to `_≐ᶜ_`, and necessarily so: the renaming zones compose their
-- renaming into the one the node stores, while the substituting zones
-- renormalise the node entirely (`unbox⇒var` then `unbox-var`), so the stored
-- renaming and boxed value do not agree on the nose — which is why `unbox-≐`
-- compares the cell alone.
--
-- The node is *returned*, together with its cell, rather than presented as an
-- `unbox-var`. Otherwise every zone's intermediate term carries a `≾ᵣ` bound
-- that unification cannot recover — `unbox-var` stores its renaming through
-- `split-pf`, so it is not invertible — and there are two such bounds per zone.
-- Returning the node keeps every bound out of the chain but one, `sub-unbox`'s,
-- which the input bound supplies explicitly through `env-cell-rel`.
--
-- The cell is a parameter given by an equation, since a substituting zone
-- retargets it: its cell is `unbox-var-tgt` of the rebuilt node.
------------------------------------------------------------------------

UnboxAt : ∀ {St Γ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
        → Tgt (Γ ++ᶜ Δ) ([ ρ ] A)
        → toCtx St ++ᶜ Δ ⊢C⦂ C → ((Γ ++ᶜ Δ) ∷ A) ⊢C⦂ C → Set
UnboxAt {St} {Γ} {A} {C} {ρ} γ Δ t N M =
  Σ[ Δ₁ ∈ Ctx ] Σ[ w₁ ∈ Ren [] (Δ₁ ⟨ ρ ⟩) (toCtx St ++ᶜ Δ) ]
  Σ[ V₁ ∈ Δ₁ ⊢V⦂ [ ρ ] A ]
    (unbox-tgt w₁ V₁ ≡ env-cell γ Δ t)
  × (N ≐ᶜ unbox w₁ V₁ (env-Cˢ γ (Δ ∷ A) M))

env-eternal-C-unbox : ∀ {Δ Γc Δ₀ A C ρ} → (lf : Lock-free Δ) → (η : ClosedVals Δ)
                    → (w : Ren [] (Δ₀ ⟨ ρ ⟩) (Δ ++ᶜ Γc)) → (V : Δ₀ ⊢V⦂ [ ρ ] A)
                    → (M : ((Δ ++ᶜ Γc) ∷ A) ⊢C⦂ C)
                    → (t : Tgt (Δ ++ᶜ Γc) ([ ρ ] A)) → unbox-tgt w V ≡ t
                    → (rel : proj₁ t ≾ᵣ ρ)
                    → Σ[ Δ₁ ∈ Ctx ] Σ[ w₁ ∈ Ren [] (Δ₁ ⟨ ρ ⟩) Γc ]
                      Σ[ V₁ ∈ Δ₁ ⊢V⦂ [ ρ ] A ]
                        (unbox-tgt w₁ V₁ ≡ env-eternal-cell lf η t)
                      × (env-eternal-C lf η (unbox w V M)
                         ≐ᶜ unbox w₁ V₁ (env-eternal-C lf η M))

env-eternal-C-unbox {[]} {Γc} {A = A} lf-[] η w V M .(unbox-tgt w V) refl rel =
    _ , castʳ (++ᶜ-identityˡ {Γc}) w , V
  , unbox-tgt-castʳ (++ᶜ-identityˡ {Γc}) w V
  , ≐ᶜ-trans (≡→≐ᶜ (cast-unbox (++ᶜ-identityˡ {Γc})))
      (unbox-≐ refl
        (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (++ᶜ-identityˡ {Γc}))
                         (++ᶜ-identityˡ {Γc ∷ A}) M)))

env-eternal-C-unbox {Δ ∷ B} {Γc} {A = A} (lf-∷ lf) η w V M
                    .(unbox-tgt w V) refl rel
  with env-eternal-C-unbox lf (λ x → η (Tl-∷ x))
         (castʳ (castOf {Δ} {B} Γc) (unbox-var-ren (proj₂ tE) relE))
         (var (λ _ → ≾ᵣ-refl) Hd)
         (castᶜ (castOf {Δ} {B} (Γc ∷ A)) (M [ Tl-∷ (bvar B Γc) ↦ W₀ ]c))
         _
         (trans (unbox-tgt-castʳ (castOf {Δ} {B} Γc)
                                  (unbox-var-ren (proj₂ tE) relE)
                                  (var (λ _ → ≾ᵣ-refl) Hd))
                (cong (Tgt-cast (castOf {Δ} {B} Γc))
                      (unbox-var-tgt (proj₂ tE) relE)))
         relE
  where
    W₀   = bval Γc (V-rename (empty-ren lf) (η Hd))
    tE   = rvar-tgt (proj₂ (unbox-tgt w V)) (bvar B Γc) W₀
    relE = ≾ᵣ-trans (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt w V) ⟩[ bvar B Γc
                                     ↦ W₀ ]rvar))) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , w₁ , V₁ , ce
  , ≐ᶜ-trans
      (env-eternal-C-≐ lf (λ x → η (Tl-∷ x))
        (≐ᶜ-trans
          (castᶜ-≐ (castOf {Δ} {B} Γc)
            (sub-unbox w V M (bvar B Γc)
                       (bval Γc (V-rename (empty-ren lf) (η Hd))) _))
          (≐ᶜ-trans
            (≡→≐ᶜ (cast-unbox (castOf {Δ} {B} Γc)))
            (unbox-≐ refl
              (≡→≐ᶜ (castᶜ-irr
                       (cong (_∷ A) (castOf {Δ} {B} Γc))
                       (castOf {Δ} {B} (Γc ∷ A)) _))))))
      eq

env-Cˢ-unbox : ∀ {St Γ Δ₀ A C ρ} → (γ : Env St Γ) → (Δ : Ctx)
             → (w : Ren [] (Δ₀ ⟨ ρ ⟩) (Γ ++ᶜ Δ)) → (V : Δ₀ ⊢V⦂ [ ρ ] A)
             → (M : ((Γ ++ᶜ Δ) ∷ A) ⊢C⦂ C)
             → (t : Tgt (Γ ++ᶜ Δ) ([ ρ ] A)) → unbox-tgt w V ≡ t
             → (rel : proj₁ t ≾ᵣ ρ)
             → UnboxAt γ Δ t (env-Cˢ γ Δ (unbox w V M)) M

env-Cˢ-unbox ⌊ St ⌋ Δ w V M .(unbox-tgt w V) refl rel =
  _ , w , V , refl , ≐ᶜ-refl _

env-Cˢ-unbox (∅ᵉ St) Δ w V M .(unbox-tgt w V) refl rel =
    _ , (cong-ren (∅-ren St) ∘ʳ w) , V
  , unbox-tgt-∘ (cong-ren (∅-ren St)) w V , ≐ᶜ-refl _

env-Cˢ-unbox (sliceᵉ γ q) Δ w V M .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ Δ w V M _ refl rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , (cong-ren (slice-renᵘ q) ∘ʳ w₁) , V₁
  , trans (unbox-tgt-∘ (cong-ren (slice-renᵘ q)) w₁ V₁)
          (cong (var-tgt′ (cong-ren (slice-renᵘ q))) ce)
  , C-rename-cong (cong-ren (slice-renᵘ q)) eq

env-Cˢ-unbox {A = A} (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ w V M
             .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
         (castʳ (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , (cong-ren (unbox-ren q) ∘ʳ castʳ eOut w₁) , V₁
  , trans (unbox-tgt-∘ (cong-ren (unbox-ren q)) (castʳ eOut w₁) V₁)
          (cong (var-tgt′ (cong-ren (unbox-ren q)))
                (trans (unbox-tgt-castʳ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)))
  , ≐ᶜ-trans
      (C-rename-cong (cong-ren (unbox-ren q))
        (castᶜ-≐ eOut
          (≐ᶜ-trans (env-Cˢ-≐ γ ([] ⟨ ρ₀ ⟩ ++ᶜ Δ)
                       (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ)))) eq)))
      (≐ᶜ-trans
        (≡→≐ᶜ (cong (C-rename (cong-ren (unbox-ren q))) (cast-unbox eOut)))
        (unbox-≐ refl
          (C-rename-cong (cong-ren (unbox-ren q))
            (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) eOut)
                     (sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) (Δ ∷ A))) _)))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

env-Cˢ-unbox {A = A} (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V₀ γ) Δ w V M
             .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
         (castʳ (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , castʳ eOut w₁ , V₁
  , trans (unbox-tgt-castʳ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)
  , ≐ᶜ-trans
      (castᶜ-≐ eOut
        (≐ᶜ-trans (env-Cˢ-≐ γ ([] ∷ [ ρ₀ ] A₀ ++ᶜ Δ)
                     (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ)))) eq))
      (≐ᶜ-trans (≡→≐ᶜ (cast-unbox eOut))
        (unbox-≐ refl
          (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) eOut)
                   (sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) (Δ ∷ A))) _))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ)

env-Cˢ-unbox (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ w V M .(unbox-tgt w V) refl rel
  with env-eternal-C-unbox lf η (castʳ (++ᶜ-assoc Δ₀ Γ₁ Δ) w) V
         (castᶜ (cong (_∷ _) (++ᶜ-assoc Δ₀ Γ₁ Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Δ₀ Γ₁ Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq
  with env-Cˢ-unbox γ Δ w₁ V₁ _ _ ce
         (env-eternal-cell-rel lf η (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ)
                                       (unbox-tgt w V)) rel)
...  | Δ₂ , w₂ , V₂ , ce₂ , eq₂ =
    Δ₂ , w₂ , V₂ , ce₂
  , ≐ᶜ-trans
      (env-Cˢ-≐ γ Δ
        (≐ᶜ-trans
          (env-eternal-C-≐ lf η
            (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Δ₀ Γ₁ Δ))))
          eq))
      (≐ᶜ-trans eq₂
        (unbox-≐ refl
          (env-Cˢ-≐ γ (Δ ∷ _)
            (env-eternal-C-≐ lf η
              (≡→≐ᶜ (castᶜ-irr (cong (_∷ _) (++ᶜ-assoc Δ₀ Γ₁ Δ))
                       (++ᶜ-assoc Δ₀ Γ₁ (Δ ∷ _)) _))))))

env-Cˢ-unbox {A = A} (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ w V M
             .(unbox-tgt w V) refl rel
  with env-Cˢ-unbox γ ([] ∷ A₀ ++ᶜ Δ)
         (castʳ (++ᶜ-assoc Γ ([] ∷ A₀) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ∷ A₀) Δ)) M)
         _ (unbox-tgt-castʳ (++ᶜ-assoc Γ ([] ∷ A₀) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    _ , castʳ cOf (unbox-var-ren z relSub) , var (λ _ → ≾ᵣ-refl) Hd
  , trans (unbox-tgt-castʳ cOf (unbox-var-ren z relSub)
                            (var (λ _ → ≾ᵣ-refl) Hd))
          (cong (Tgt-cast cOf)
            (trans (unbox-var-tgt z relSub)
                   (cong (λ u → rvar-tgt (proj₂ u) (bvar A₀ Δ) (bval Δ W))
                         ceOut)))
  , ≐ᶜ-trans
      (castᶜ-≐ cOf
        (≐ᶜ-trans
          (sub-≐ᶜ (bvar A₀ Δ) (≐ᵛ-refl (bval Δ W))
            (≐ᶜ-trans
              (castᶜ-≐ eOut
                (≐ᶜ-trans
                  (env-Cˢ-≐ γ ([] ∷ A₀ ++ᶜ Δ)
                    (≡→≐ᶜ (cast-unbox (++ᶜ-assoc Γ ([] ∷ A₀) Δ))))
                  eq))
              (≡→≐ᶜ (cast-unbox eOut))))
          (sub-unbox (castʳ eOut w₁) V₁ _ (bvar A₀ Δ) (bval Δ W) relSub)))
      (≐ᶜ-trans (≡→≐ᶜ (cast-unbox cOf))
        (unbox-≐ refl
          (≐ᶜ-trans
            (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) cOf)
                     (castOf {toCtx St} {A₀} (Δ ∷ A)) _))
            (castᶜ-≐ (castOf {toCtx St} {A₀} (Δ ∷ A))
              (sub-≐ᶜ (bvar A₀ (Δ ∷ A))
                (≡→≐ᵛ (castᵛ-irr _ _ W))
                (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) eOut)
                         (sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) (Δ ∷ A)))
                         _)))))))
  where
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)
    cOf  = castOf {toCtx St} {A₀} Δ

    ceOut = trans (unbox-tgt-castʳ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)

    relSub =
      ≾ᵣ-trans
        (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt (castʳ eOut w₁) V₁) ⟩[ bvar A₀ Δ
                         ↦ bval Δ W ]rvar)))
        (subst (_≾ᵣ _) (sym (cong proj₁ ceOut))
          (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ)
            (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) (unbox-tgt w V)) rel))

    z = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳ eOut w₁) V₁))
                        (bvar A₀ Δ) (bval Δ W))

------------------------------------------------------------------------
-- THE CELL ACTION, SUFFIX-FREE
--
-- `env-cell` recurses through *growing* suffixes, so a statement that only
-- makes sense at the empty one — such as "the cell's content is reducible",
-- whose `lookup-body` needs the cell to land in `toCtx St` — cannot be proved
-- against it by induction on the environment. This is the same action read
-- off the environment's zones directly, where the recursion stays at the
-- boundary and every case is a variable of `toCtx St`.
--
-- Two zones are discharged rather than computed. `∅ᵉ` has no variables; and an
-- eternal prefix has no *cell*, because the value it would substitute is a
-- closed one of box type, hence a variable of `[]` (`grad-typ⇒var`).
------------------------------------------------------------------------

env-cell₀ : ∀ {St Γ A ρ} → (γ : Env St Γ)
          → Tgt Γ ([ ρ ] A) → Tgt (toCtx St) ([ ρ ] A)

-- a cell cannot come from an eternal prefix
eternal-no-cell : ∀ {Δ₀ A ρ σ} → (η : ClosedVals Δ₀)
                → [ ρ ] A ∈[ σ ] Δ₀ → ⊥
eternal-no-cell η x =
  not-in-empty-ctx (proj₁ (proj₂ (grad-typ⇒var (η x))))

env-cell₀ ⌊ St ⌋      t         = t
env-cell₀ (∅ᵉ St)     (σ , x)   = ⊥-elim (not-in-empty-ctx x)
env-cell₀ (sliceᵉ γ q) t        = var-tgt′ (slice-renᵘ q) (env-cell₀ γ t)

env-cell₀ (_⟨_⟩ᵉ {ρ = ρ₀} γ q) (σ , Tl-⟨⟩ y) =
  var-tgt′ (unbox-ren q) (Tgt-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))

env-cell₀ (γ ∷ᵉ W) (σ , Hd)     =
  proj₁ (grad-typ⇒var W) , proj₁ (proj₂ (grad-typ⇒var W))
env-cell₀ (γ ∷ᵉ W) (σ , Tl-∷ y) = env-cell₀ γ (σ , y)

env-cell₀ (liftᵉ V γ) (σ , Hd)     = uᵣ , Hd
env-cell₀ (liftᵉ V γ) (σ , Tl-∷ y) = Tgt-∷ (env-cell₀ γ (σ , y))

env-cell₀ (eternalˡ Δ₀ lf η γ) (σ , x)
  with ∈-++ᶜ-split Δ₀ _ x
... | inj₁ (ρ' , y) = ⊥-elim (eternal-no-cell η y)
... | inj₂ y        = env-cell₀ γ (σ , y)

------------------------------------------------------------------------
-- THE CELL THE ENVIRONMENT SENDS A CELL TO IS REDUCIBLE
--
-- This is `Val` at the box type, for `env-cell₀ γ t` — which is what makes the
-- two substituting zones nothing at all: `_∷ᵉ_`'s cell is the value the zone
-- substitutes, and `Rel-Env` already says that value is `Val` at its box type;
-- `liftᵉ`'s is the freshly allocated cell, and `Rel-Env`'s Kripke component is
-- exactly `store-fresh`'s hypothesis. Both were unreachable while `Val` at a
-- box type quantified over a slice rather than over readability.
------------------------------------------------------------------------

env-cell₀-val : ∀ {St Γ A ρ} → (γ : Env St Γ) → Rel-Env γ
              → (t : Tgt Γ ([ ρ ] A))
              → ∀ {St'} → (e : St ≤ₛ St')
              → (rel : proj₁ (≤ₛ-embed e (proj₂ (env-cell₀ γ t))) ≾ᵣ ρ)
              --------------------------------------------------------------
              → Val A St' (lookup-body St' (≤ₛ-embed e (proj₂ (env-cell₀ γ t)))
                                       rel)

env-cell₀-val ⌊ St ⌋   pγ t       e rel = pγ e (proj₂ t) rel
env-cell₀-val (∅ᵉ St)  pγ (σ , x) e rel = ⊥-elim (not-in-empty-ctx x)

env-cell₀-val {A = A} {ρ = ρ} (sliceᵉ γ q) pγ t {St'} e rel =
  Val-≐ᵛ A (≡→≐ᵛ (lookup-body-≡ St' cellEq rel₁ rel))
           (env-cell₀-val γ pγ t (≤ₛ-trans (ext q) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ t)

    cellEq = trans (≤ₛ-embed-∘ (ext q) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (slice-renᵘ-tgt q c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val {A = A} {ρ = ρ} (_⟨_⟩ᵉ {ρ = ρ₀} γ q) pγ (σ , Tl-⟨⟩ y) {St'} e rel =
  Val-≐ᵛ A (≡→≐ᵛ (lookup-body-≡ St' cellEq rel₁ rel))
           (env-cell₀-val γ pγ (_ , y) (≤ₛ-trans (ext q) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ (_ , y))

    cellEq = trans (≤ₛ-embed-∘ (ext q) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (unbox-ren-tgt q c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Hd)     e rel = pW e rel
env-cell₀-val (γ ∷ᵉ W) (pγ , pW) (σ , Tl-∷ y) e rel =
  env-cell₀-val γ pγ (σ , y) e rel

env-cell₀-val (liftᵉ V γ) (pγ , pV) (σ , Hd) e rel =
  store-fresh V pV (λ _ → ≾ᵣ-refl) e rel

env-cell₀-val {A = A} {ρ = ρ} (liftᵉ V γ) (pγ , pV) (σ , Tl-∷ y) {St'} e rel =
  Val-≐ᵛ A (≡→≐ᵛ (lookup-body-≡ St' cellEq rel₁ rel))
           (env-cell₀-val γ pγ (σ , y) (≤ₛ-trans (∷-suc V id-suc) e) rel₁)
  where
    c = proj₂ (env-cell₀ γ (σ , y))

    cellEq = ≤ₛ-embed-∘ (∷-suc V id-suc) e c
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

env-cell₀-val (eternalˡ Δ₀ lf η γ) (pγ , et) (σ , x) e rel
  with ∈-++ᶜ-split Δ₀ _ x
... | inj₁ (ρ' , y) = ⊥-elim (eternal-no-cell η y)
... | inj₂ y        = env-cell₀-val γ pγ (σ , y) e rel

------------------------------------------------------------------------
-- THE TWO CELL ACTIONS AGREE
--
-- `env-cell` recurses through growing suffixes, `env-cell₀` stays at the
-- boundary. They agree on the cells that matter — those pushed in from the
-- environment's own context — which is all `FL-unbox` reads, the suffix being
-- empty there.
------------------------------------------------------------------------

Tgt-++ᶜˡ : ∀ {Γ A} → (Δ : Ctx) → Tgt Γ A → Tgt (Γ ++ᶜ Δ) A
Tgt-++ᶜˡ Δ (σ , x) = grade-++ᶜˡ σ Δ , ∈-++ᶜˡ Δ x

Tgt-cast-loop : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (t : Tgt Γ' A)
              → Tgt-cast e (Tgt-cast (sym e) t) ≡ t
Tgt-cast-loop refl t = refl

-- A cell that comes from the *suffix* is left where it is: `cong-ren` is the
-- identity on the suffix, and a substituting zone's boundary variable is not a
-- suffix variable, so `⟨_⟩[_↦_]rvar` leaves it alone (`sub-rvar-r`). This is
-- what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` below need, the boundary entry being
-- a suffix cell at the suffix the zone recurses at.

-- Substituting *at* a resource variable, rather than past it: the counterpart
-- of `sub-rvar-r`, and what the `Hd` halves of `_∷ᵉ_`/`liftᵉ` need. The value
-- put in the variable's place is of box type, hence a variable itself, and the
-- result is that variable pushed back under the suffix.

rvar-hit : ∀ {Γ A ρ} → (Θ : Ctx)
         → (W : split-l (bvar {Γ} ([ ρ ] A) Θ) ⊢V⦂ [ ρ ] A)
         → rvar-tgt (bvar {Γ} ([ ρ ] A) Θ) (bvar {Γ} ([ ρ ] A) Θ) W
         ≡ Tgt-++ᶜˡ (split-r (bvar {Γ} ([ ρ ] A) Θ)) (val-cell W)

rvar-hit []        W = refl
rvar-hit (Θ ∷ C)   W = cong Tgt-∷ (rvar-hit Θ W)
rvar-hit (Θ ⟨ ρ' ⟩) W = cong (Tgt-⟨⟩ ρ') (rvar-hit Θ W)

-- A transport of a concatenation acts on the cell by its prefix half and on
-- the push by its suffix half — which is what `castOf`, being a `cong₂`, is.

Tgt-cast-++ᶜˡ : ∀ {Γ₁ Γ₂ A} → (e₁ : Γ₁ ≡ Γ₂) → {Θ₁ Θ₂ : Ctx} → (e₂ : Θ₁ ≡ Θ₂)
              → (t : Tgt Γ₁ A)
              → Tgt-cast (cong₂ _++ᶜ_ e₁ e₂) (Tgt-++ᶜˡ Θ₁ t)
              ≡ Tgt-++ᶜˡ Θ₂ (Tgt-cast e₁ t)
Tgt-cast-++ᶜˡ refl refl t = refl

-- The cell a box-typed value names travels with a transport of its context.

val-cell-cast : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (W : Γ ⊢V⦂ [ ρ ] A)
              → val-cell (castᵛ e W) ≡ Tgt-cast e (val-cell W)
val-cell-cast refl W = refl

∈-++ᶜʳ-assoc⁻ : ∀ {A ρ} → (Γ Γ' : Ctx) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
              → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ))
                      (∈-++ᶜʳ {Γ = Γ} (∈-++ᶜʳ {Γ = Γ'} x))
              ≡ ∈-++ᶜʳ {Γ = Γ ++ᶜ Γ'} x
∈-++ᶜʳ-assoc⁻ Γ Γ' {Δ} x =
  trans (cong (subst (λ Γ₀ → _ ∈[ _ ] Γ₀) (sym (++ᶜ-assoc Γ Γ' Δ)))
              (sym (∈-++ᶜʳ-assoc Γ Γ' x)))
        (subst-sym-subst′ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))

env-eternal-cell-suffix : ∀ {Δ₀ Γc A ρ σ} → (lf : Lock-free Δ₀)
                        → (η : ClosedVals Δ₀) → (z : [ ρ ] A ∈[ σ ] Γc)
                        → env-eternal-cell lf η (σ , ∈-++ᶜʳ {Γ = Δ₀} z)
                        ≡ (σ , z)

env-eternal-cell-suffix lf-[] η z =
  cong (λ v → _ , v) (∈-++ᶜʳ-[] z)
env-eternal-cell-suffix {Δ ∷ B} {Γc} (lf-∷ lf) η z =
  trans (cong (env-eternal-cell lf (λ x → η (Tl-∷ x)))
              (sub-rvar-r Γc z (bval Γc (V-rename (empty-ren lf) (η Hd)))))
        (env-eternal-cell-suffix lf (λ x → η (Tl-∷ x)) z)

env-cell-suffix : ∀ {St Γ A ρ σ} → (γ : Env St Γ) → (Δ : Ctx)
                → (z : [ ρ ] A ∈[ σ ] Δ)
                → env-cell γ Δ (σ , ∈-++ᶜʳ {Γ = Γ} z)
                ≡ (σ , ∈-++ᶜʳ {Γ = toCtx St} z)

env-cell-suffix ⌊ St ⌋  Δ z = refl
env-cell-suffix (∅ᵉ St) Δ z = cong-ren-tgt-r (∅-ren St) z
env-cell-suffix (sliceᵉ γ q) Δ z =
  trans (cong (var-tgt′ (cong-ren (slice-renᵘ q))) (env-cell-suffix γ Δ z))
        (cong-ren-tgt-r (slice-renᵘ q) z)

env-cell-suffix (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ z =
  trans (cong (λ v → var-tgt′ (cong-ren (unbox-ren q))
                       (Tgt-cast eOut (env-cell γ Δ' (_ , v))))
              (∈-++ᶜʳ-assoc Γ ([] ⟨ ρ₀ ⟩) z))
    (trans (cong (λ v → var-tgt′ (cong-ren (unbox-ren q)) (Tgt-cast eOut v))
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ⟨ ρ₀ ⟩} z)))
      (trans (cong (λ v → var-tgt′ (cong-ren (unbox-ren q)) (_ , v))
                   (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ⟨ ρ₀ ⟩) z))
             (cong-ren-tgt-r (unbox-ren q) z)))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

env-cell-suffix (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ z =
  trans (cong (λ v → Tgt-cast eOut (env-cell γ Δ' (_ , v)))
              (∈-++ᶜʳ-assoc Γ ([] ∷ [ ρ₀ ] A₀) z))
    (trans (cong (Tgt-cast eOut)
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ [ ρ₀ ] A₀} z)))
           (cong (λ v → _ , v) (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ∷ [ ρ₀ ] A₀) z)))
  where
    Δ'   = [] ∷ [ ρ₀ ] A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ [ ρ₀ ] A₀) Δ)

env-cell-suffix (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ z =
  trans (cong (λ v → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                       (rvar-tgt (proj₂ (Tgt-cast eOut (env-cell γ Δ' (_ , v))))
                                 (bvar A₀ Δ) (bval Δ W)))
              (∈-++ᶜʳ-assoc Γ ([] ∷ A₀) z))
    (trans (cong (λ v → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                          (rvar-tgt (proj₂ (Tgt-cast eOut v))
                                    (bvar A₀ Δ) (bval Δ W)))
                 (env-cell-suffix γ Δ' (∈-++ᶜʳ {Γ = [] ∷ A₀} z)))
      (trans (cong (λ v → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                            (rvar-tgt v (bvar A₀ Δ) (bval Δ W)))
                   (∈-++ᶜʳ-assoc⁻ (toCtx St) ([] ∷ A₀) z))
             (sub-rvar-r Δ z (bval Δ W))))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

env-cell-suffix (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ z =
  trans (cong (λ v → env-cell γ Δ (env-eternal-cell lf η (_ , v)))
              (∈-++ᶜʳ-assoc Δ₀ Γ₁ z))
    (trans (cong (env-cell γ Δ)
                 (env-eternal-cell-suffix lf η (∈-++ᶜʳ {Γ = Γ₁} z)))
           (env-cell-suffix γ Δ z))

env-cell-push : ∀ {St Γ A ρ} → (γ : Env St Γ) → (Δ : Ctx)
              → (t : Tgt Γ ([ ρ ] A))
              → env-cell γ Δ (Tgt-++ᶜˡ Δ t) ≡ Tgt-++ᶜˡ Δ (env-cell₀ γ t)

env-cell-push ⌊ St ⌋  Δ t       = refl
env-cell-push (∅ᵉ St) Δ (σ , x) = ⊥-elim (not-in-empty-ctx x)

env-cell-push (sliceᵉ γ q) Δ t =
  trans (cong (var-tgt′ (cong-ren (slice-renᵘ q))) (env-cell-push γ Δ t))
        (cong-ren-tgt-l (slice-renᵘ q) Δ (proj₂ (env-cell₀ γ t)))

-- The two zones that grow the suffix by a binder split on the variable. A
-- `Tl-∷` is the `⟨⟩ᵉ` pattern with `[] ∷ A₀` for `[] ⟨ ρ₀ ⟩`; a `Hd` is the
-- zone's own boundary variable, which `∈-++ᶜˡ-++ᶜʳ` recognises as a *suffix*
-- variable of the grown suffix, so `env-cell-suffix` carries it across. At
-- `_∷ᵉ_` the substitution then hits it (`split→∈-∈-++ᶜˡ` identifies the pushed
-- boundary variable with `bvar`, and `rvar-hit` reads off the substituted
-- value's own cell); at `liftᵉ` nothing substitutes and it stays the fresh
-- cell. The eternal zone has no cell of its own at all.

env-cell-push (_⟨_⟩ᵉ {St = St} {Γ = Γ} {ρ = ρ₀} γ q) Δ (σ , Tl-⟨⟩ y) =
  trans (cong (λ z → var-tgt′ (cong-ren (unbox-ren q))
                       (Tgt-cast eOut (env-cell γ Δ' z)))
              step-in)
    (trans (cong (λ z → var-tgt′ (cong-ren (unbox-ren q)) (Tgt-cast eOut z))
                 (env-cell-push γ Δ' (_ , y)))
      (trans (cong (var-tgt′ (cong-ren (unbox-ren q)))
                   (∈-++ᶜˡ-assoc {Γ = toCtx St} ([] ⟨ ρ₀ ⟩) Δ
                                 (proj₂ (env-cell₀ γ (_ , y)))))
             (cong-ren-tgt-l (unbox-ren q) Δ
                             (proj₂ (Tgt-⟨⟩ ρ₀ (env-cell₀ γ (_ , y)))))))
  where
    Δ'   = [] ⟨ ρ₀ ⟩ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ⟨ ρ₀ ⟩) Δ)

    -- `Tl-⟨⟩ y` *is* the push of `y` under `[] ⟨ ρ₀ ⟩`, so the zone's
    -- associativity cast just re-brackets the two pushes
    step-in : Tgt-cast eIn (Tgt-++ᶜˡ Δ (σ , Tl-⟨⟩ y))
            ≡ Tgt-++ᶜˡ Δ' (_ , y)
    step-in =
      trans (cong (Tgt-cast eIn)
                  (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ⟨ ρ₀ ⟩) Δ y)))
            (Tgt-cast-loop eIn (Tgt-++ᶜˡ Δ' (_ , y)))
env-cell-push (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                       (rvar-tgt (proj₂ (Tgt-cast eOut (env-cell γ Δ' z)))
                                 (bvar A₀ Δ) (bval Δ W)))
              step-in)
    (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                          (rvar-tgt (proj₂ (Tgt-cast eOut z))
                                    (bvar A₀ Δ) (bval Δ W)))
                 (env-cell-push γ Δ' (σ , y)))
      (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                            (rvar-tgt (proj₂ z) (bvar A₀ Δ) (bval Δ W)))
                   (∈-++ᶜˡ-assoc {Γ = toCtx St} ([] ∷ A₀) Δ c))
             (sub-rvar-l Δ c (bval Δ W))))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ ([] ∷ A₀) Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

    c = proj₂ (env-cell₀ γ (σ , y))

    step-in : Tgt-cast eIn (Tgt-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Tgt-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Tgt-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} ([] ∷ A₀) Δ y)))
            (Tgt-cast-loop eIn (Tgt-++ᶜˡ Δ' (σ , y)))

env-cell-push (_∷ᵉ_ {St = St} {Γ = Γ} {A = A₀} γ W) Δ (σ , Hd) =
  trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                       (rvar-tgt (proj₂ (Tgt-cast eOut (env-cell γ Δ' z)))
                                 (bvar A₀ Δ) (bval Δ W)))
              (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ A₀) Δ Hd))
    (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                          (rvar-tgt (proj₂ (Tgt-cast eOut z))
                                    (bvar A₀ Δ) (bval Δ W)))
                 (env-cell-suffix γ Δ' bnd))
      (trans (cong (λ z → Tgt-cast (castOf {toCtx St} {A₀} Δ)
                            (rvar-tgt (proj₂ z) (bvar A₀ Δ) (bval Δ W)))
                   (trans step-out (sym (split→∈-∈-++ᶜˡ (toCtx St) A₀ Δ))))
        (trans (cong (Tgt-cast (castOf {toCtx St} {A₀} Δ))
                     (rvar-hit Δ (bval Δ W)))
               fin)))
  where
    Δ'   = [] ∷ A₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ)

    bnd = ∈-++ᶜˡ {Γ = [] ∷ A₀} Δ Hd

    -- the boundary variable, come across, is `Hd` pushed under the suffix
    step-out : Tgt-cast eOut (grade-++ᶜˡ uᵣ Δ , ∈-++ᶜʳ {Γ = toCtx St} bnd)
             ≡ Tgt-++ᶜˡ Δ (uᵣ , Hd {Γ = toCtx St})
    step-out =
      Tgt-cast-flip (++ᶜ-assoc (toCtx St) ([] ∷ A₀) Δ) _ _
                    (∈-++ᶜˡ-++ᶜʳ (toCtx St) ([] ∷ A₀) Δ Hd)

    -- `bval` transports the value into `split-l`; `castOf` transports it back
    fin : Tgt-cast (castOf {toCtx St} {A₀} Δ)
            (Tgt-++ᶜˡ (split-r (bvar {toCtx St} A₀ Δ)) (val-cell (bval Δ W)))
        ≡ Tgt-++ᶜˡ Δ (val-cell W)
    fin =
      trans (Tgt-cast-++ᶜˡ (split→∈-split-l (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))
                           (split→∈-split-r (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))
                           (val-cell (bval Δ W)))
            (cong (Tgt-++ᶜˡ Δ)
              (trans (cong (Tgt-cast (split→∈-split-l
                                        (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ})))
                           (val-cell-cast (sym (split→∈-split-l
                                        (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))) W))
                     (Tgt-cast-loop (split→∈-split-l
                                      (split-≡-++ᶜ {toCtx St ∷ A₀} {Δ}))
                                    (val-cell W))))

env-cell-push (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Tl-∷ y) =
  trans (cong (λ z → Tgt-cast eOut (env-cell γ Δ' z)) step-in)
    (trans (cong (Tgt-cast eOut) (env-cell-push γ Δ' (σ , y)))
           (∈-++ᶜˡ-assoc {Γ = toCtx St} B₀ Δ (proj₂ (env-cell₀ γ (σ , y)))))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eIn  = ++ᶜ-assoc Γ B₀ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) B₀ Δ)

    step-in : Tgt-cast eIn (Tgt-++ᶜˡ Δ (σ , Tl-∷ y)) ≡ Tgt-++ᶜˡ Δ' (σ , y)
    step-in =
      trans (cong (Tgt-cast eIn) (sym (∈-++ᶜˡ-assoc {Γ = Γ} B₀ Δ y)))
            (Tgt-cast-loop eIn (Tgt-++ᶜˡ Δ' (σ , y)))

env-cell-push (liftᵉ {St = St} {Γ = Γ} {A = A₀} {ρ = ρ₀} V γ) Δ (σ , Hd) =
  trans (cong (λ z → Tgt-cast eOut (env-cell γ Δ' z))
              (∈-++ᶜˡ-++ᶜʳ Γ B₀ Δ Hd))
    (trans (cong (Tgt-cast eOut) (env-cell-suffix γ Δ' bnd))
           (Tgt-cast-flip (++ᶜ-assoc (toCtx St) B₀ Δ) _ _
                          (∈-++ᶜˡ-++ᶜʳ (toCtx St) B₀ Δ Hd)))
  where
    B₀   = [] ∷ [ ρ₀ ] A₀
    Δ'   = B₀ ++ᶜ Δ
    eOut = sym (++ᶜ-assoc (toCtx St) B₀ Δ)

    bnd = ∈-++ᶜˡ {Γ = B₀} Δ Hd

env-cell-push (eternalˡ {Γ = Γ₁} Δ₀ lf η γ) Δ (σ , x)
  with ∈-++ᶜ-split Δ₀ Γ₁ x in eq

... | inj₁ (ρ' , y) = ⊥-elim (eternal-no-cell η y)

... | inj₂ y =
  trans (cong (λ z → env-cell γ Δ
                       (env-eternal-cell lf η
                         (Tgt-cast (++ᶜ-assoc Δ₀ Γ₁ Δ) (Tgt-++ᶜˡ Δ (σ , z)))))
              (∈-++ᶜ-split-inj₂ Δ₀ Γ₁ x y eq))
    (trans (cong (λ z → env-cell γ Δ (env-eternal-cell lf η z))
                 (∈-++ᶜˡ-++ᶜʳ Δ₀ Γ₁ Δ y))
      (trans (cong (env-cell γ Δ)
                   (env-eternal-cell-suffix lf η (∈-++ᶜˡ {Γ = Γ₁} Δ y)))
             (env-cell-push γ Δ (σ , y))))
