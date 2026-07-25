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
--   * `renᵉ`    — precomposition with a renaming, making `Env`       --
--                 functorial (`env-alloc`);                          --
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

open import Relation.Nullary using (yes; no)

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

-- LOCK-FREE CONTEXTS
--
-- `_ᴱ` drops every lock, so the eternal prefix is lock-free — which is what
-- makes a closed value weakenable into it: `Ren [] Γ` exists exactly when `Γ`
-- has no lock, crossing one needing `ρ ≾ᵣ uᵣ`.

data Lock-free : Ctx → Set where
  lf-[] : Lock-free []
  lf-∷  : ∀ {Γ A} → Lock-free Γ → Lock-free (Γ ∷ A)

ᴱ-lock-free : (Γ : Ctx) → Lock-free (Γ ᴱ)
ᴱ-lock-free []        = lf-[]
ᴱ-lock-free (Γ ∷ A)   with eternal? A
... | yes _           = lf-∷ (ᴱ-lock-free Γ)
... | no  _           = ᴱ-lock-free Γ
ᴱ-lock-free (Γ ⟨ ρ ⟩) = ᴱ-lock-free Γ

-- Weakening a closed term into a lock-free context, and a term into one
-- left-extended by a lock-free prefix.

empty-ren : ∀ {Δ} → Lock-free Δ → Ren [] Δ
empty-ren lf-[]     = id-ren
empty-ren (lf-∷ lf) = wk-ren ∘ʳ empty-ren lf

eternal-wk : ∀ {Δ} → Lock-free Δ → (Γ : Ctx) → Ren Γ (Δ ++ᶜ Γ)
eternal-wk lf []        = empty-ren lf
eternal-wk lf (Γ ∷ A)   = cong-∷-ren (eternal-wk lf Γ)
eternal-wk lf (Γ ⟨ ρ ⟩) = cong-⟨⟩-ren (eternal-wk lf Γ)

-- A closing environment: how `Γ` is closed down to the state context.

infixl 30 _∷ᵉ_
infix  32 _⟨_⟩ᵉ

data Env : (St : 𝕊 []) → Ctx → Set where

  ⌊_⌋      : (St : 𝕊 [])
           ------------------
           → Env St (toCtx St)

  -- precomposition with a renaming: what makes `Env` functorial in the
  -- state (`env-alloc`). Kept separate from `⌊_⌋` so that the identity
  -- case of the action stays `refl`, `Ren` being unquotiented.

  renᵉ     : ∀ {St Γ Γ₀}
           → Env St Γ → Ren Γ₀ Γ
           ---------------------
           → Env St Γ₀

  -- a lock, matched by any state far enough ahead

  _⟨_⟩ᵉ    : ∀ {St St' Γ ρ}
           → Env St Γ → Slice St ρ St' uᵣ
           ------------------------------
           → Env St' (Γ ⟨ ρ ⟩)

  _∷ᵉ_     : ∀ {St Γ A}
           → Env St Γ → toCtx St ⊢V⦂ A
           ---------------------------
           → Env St (Γ ∷ A)

  eternalˡ : ∀ {St Γ}
           → (Δ : Ctx) → Lock-free Δ → ClosedVals Δ → Env St Γ
           ---------------------------------------------------
           → Env St (Δ ++ᶜ Γ)

-- REDUCIBLE ENVIRONMENTS
--
-- The state's own part is the store; each instantiated binder holds a
-- reducible value; the eternal prefix holds closed constants, of which nothing
-- is asked (eternal types are base/unit/products).

Rel-Env : ∀ {St Γ} → Env St Γ → Set
Rel-Env ⌊ St ⌋                = Store St
Rel-Env (γ ⟨ q ⟩ᵉ)             = Rel-Env γ
Rel-Env (_∷ᵉ_ {St} {Γ} {A} γ V) = Rel-Env γ × Val A St V
Rel-Env (renᵉ γ r)             = Rel-Env γ
Rel-Env (eternalˡ Δ lf η γ)    = Rel-Env γ

-- RETYPING ALONG A CONTEXT EQUALITY

castᵛ : ∀ {Γ Γ' A} → Γ ≡ Γ' → Γ ⊢V⦂ A → Γ' ⊢V⦂ A
castᵛ refl V = V

castᶜ : ∀ {Γ Γ' C} → Γ ≡ Γ' → Γ ⊢C⦂ C → Γ' ⊢C⦂ C
castᶜ refl M = M

-- A cast is irrelevant in its equality proof (UIP), and passes through a
-- binder: the two facts that let the structural laws below be stated with
-- whichever proof each side happens to produce.

castᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢V⦂ A) → castᵛ e V ≡ castᵛ e' V
castᵛ-irr e e' V = cong (λ z → castᵛ z V) uip

castᶜ-irr : ∀ {Γ Γ' C} → (e e' : Γ ≡ Γ') → (M : Γ ⊢C⦂ C) → castᶜ e M ≡ castᶜ e' M
castᶜ-irr e e' M = cong (λ z → castᶜ z M) uip

cast-lam : ∀ {Γ Γ' A B ε} → (e : Γ ≡ Γ') → (M : Γ ∷ A ⊢C⦂ B ‼ ε)
         → castᵛ e (lam M) ≡ lam (castᶜ (cong (_∷ A) e) M)
cast-lam refl M = refl

cast-const : ∀ {Γ Γ' b} → (e : Γ ≡ Γ') → {c : BaseConstants b}
           → castᵛ e (const c) ≡ const c
cast-const refl = refl

cast-⋆ : ∀ {Γ Γ'} → (e : Γ ≡ Γ') → castᵛ e ⋆ ≡ ⋆
cast-⋆ refl = refl

cast-pair : ∀ {Γ Γ' A B} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A} → {W : Γ ⊢V⦂ B}
          → castᵛ e ⦉ V , W ⦊ ≡ ⦉ castᵛ e V , castᵛ e W ⦊
cast-pair refl = refl

cast-ret : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A}
         → castᶜ e (return V) ≡ return (castᵛ e V)
cast-ret refl = refl

cast-app : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ A ⇒ C} → {W : Γ ⊢V⦂ A}
         → castᶜ e (V · W) ≡ (castᵛ e V) · (castᵛ e W)
cast-app refl = refl

cast-absurd : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {V : Γ ⊢V⦂ Empty}
            → castᶜ {C = C} e (absurd V) ≡ absurd (castᵛ e V)
cast-absurd refl = refl

cast-coerce : ∀ {Γ Γ' A ε ε'} → (e : Γ ≡ Γ') → {p : ε ≾ₑ ε'} → {M : Γ ⊢C⦂ A ‼ ε}
            → castᶜ e (coerce p M) ≡ coerce p (castᶜ e M)
cast-coerce refl = refl

-- The binding formers put their body at an *extended* context, so the cast
-- transported there is `cong` of the extension.

cast-delay : ∀ {Γ Γ' A ε τ} → (e : Γ ≡ Γ')
           → {M : Γ ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε}
           → castᶜ e (delay τ M) ≡ delay τ (castᶜ (cong (_⟨ of-natʳ τ ⟩) e) M)
cast-delay refl = refl

cast-perform : ∀ {Γ Γ' A ε} → (e : Γ ≡ Γ') → {op : Op}
             → {V : Γ ⊢V⦂ type-of-gtype (param op)}
             → {M : Γ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                      ⊢C⦂ A ‼ ε}
             → castᶜ e (perform op V M)
             ≡ perform op (castᵛ e V)
                 (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                         ∷ type-of-gtype (arity op)) e) M)
cast-perform refl = refl

cast-match : ∀ {Γ Γ' A B C} → (e : Γ ≡ Γ')
           → {V : Γ ⊢V⦂ A |×| B} → {M : Γ ∷ A ∷ B ⊢C⦂ C}
           → castᶜ e (match V `in M)
           ≡ match (castᵛ e V) `in (castᶜ (cong (λ Γ₀ → Γ₀ ∷ A ∷ B) e) M)
cast-match refl = refl

cast-box : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ')
         → {V : Γ ⟨ ρ ⟩ ⊢V⦂ A} → {M : Γ ∷ [ ρ ] A ⊢C⦂ C}
         → castᶜ e (box V M)
         ≡ box (castᵛ (cong (_⟨ ρ ⟩) e) V) (castᶜ (cong (_∷ [ ρ ] A) e) M)
cast-box refl = refl

cast-seq : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
         → {M : Γ ⊢C⦂ A ‼ ε} → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
         → castᶜ e (M ⨟ N)
         ≡ (castᶜ e M) ⨟ (castᶜ (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) e) N)
cast-seq refl = refl

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
env-Vˢ (renᵉ γ r) Δ V = env-Vˢ γ Δ (V-rename (cong-ren r) V)
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
env-Vˢ (eternalˡ Δ₀ lf η γ) Δ V =
  env-Vˢ γ Δ (env-eternal-V lf η (castᵛ (++ᶜ-assoc Δ₀ _ Δ) V))

env-Cˢ ⌊ St ⌋ Δ M = M
env-Cˢ (renᵉ γ r) Δ M = env-Cˢ γ Δ (C-rename (cong-ren r) M)
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
env-Vˢ-lam (renᵉ γ r) Δ M = env-Vˢ-lam γ Δ _

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
env-Cˢ-ret (renᵉ γ r) Δ V = env-Cˢ-ret γ Δ _

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
env-Cˢ-app (renᵉ γ r) Δ V U = env-Cˢ-app γ Δ _ _

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
env-Cˢ-absurd (renᵉ γ r) Δ V = env-Cˢ-absurd γ Δ _

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
env-Cˢ-coerce (renᵉ γ r) Δ M = env-Cˢ-coerce γ Δ _

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
env-Vˢ-pair (renᵉ γ r) Δ V U = env-Vˢ-pair γ Δ _ _

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
env-Vˢ-const (renᵉ γ r) Δ c = env-Vˢ-const γ Δ _

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
env-Vˢ-⋆ (renᵉ γ r) Δ  = env-Vˢ-⋆ γ Δ

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
env-Cˢ-delay (renᵉ γ r) Δ M = env-Cˢ-delay γ Δ _

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
env-Cˢ-seq (renᵉ γ r) Δ M N = env-Cˢ-seq γ Δ _ _

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
env-Cˢ-perform (renᵉ γ r) Δ V M = env-Cˢ-perform γ Δ _ _

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
env-Cˢ-match (renᵉ γ r) Δ V M = env-Cˢ-match γ Δ _ _

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
env-Cˢ-box (renᵉ γ r) Δ V M = env-Cˢ-box γ Δ _ _

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

-- THE ETERNAL RESTRICTION OF AN ENVIRONMENT
--
-- A handler clause closes over `Γ ᴱ` (`Language.agda:153`), so the `handle`
-- case of the fundamental lemma needs closed values for it. They are there:
-- the state contributes nothing (`toCtxᴱ-[]` — cells are box-typed, never
-- eternal), an eternal-typed telescope entry is a value over `toCtx St` of
-- eternal type and so *is* closed (`eternal-val-restrict`), and the eternal
-- prefix already holds closed values.

-- A variable of the eternal restriction comes from the context itself.

∈-ᴱ⁻ : ∀ {A ρ} → (Δ : Ctx) → A ∈[ ρ ] Δ ᴱ → Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ
∈-ᴱ⁻ []        x with x
... | ()
∈-ᴱ⁻ (Δ ∷ B)   x with eternal? B
∈-ᴱ⁻ (Δ ∷ B)   Hd       | yes _ = uᵣ , Hd
∈-ᴱ⁻ (Δ ∷ B)   (Tl-∷ y) | yes _ with ∈-ᴱ⁻ Δ y
... | ρ' , z = ρ' , Tl-∷ z
∈-ᴱ⁻ (Δ ∷ B)   x        | no  _ with ∈-ᴱ⁻ Δ x
... | ρ' , z = ρ' , Tl-∷ z
∈-ᴱ⁻ (Δ ⟨ ρ ⟩) x with ∈-ᴱ⁻ Δ x
... | ρ' , z = ρ' ·ᵣ ρ , Tl-⟨⟩ z

-- Every variable of the eternal restriction has eternal type.

ᴱ-eternal : ∀ {A ρ} → (Δ : Ctx) → A ∈[ ρ ] Δ ᴱ → Eternal A
ᴱ-eternal []        x with x
... | ()
ᴱ-eternal (Δ ∷ B)   x with eternal? B
ᴱ-eternal (Δ ∷ B)   Hd       | yes et = et
ᴱ-eternal (Δ ∷ B)   (Tl-∷ y) | yes _  = ᴱ-eternal Δ y
ᴱ-eternal (Δ ∷ B)   x        | no  _  = ᴱ-eternal Δ x
ᴱ-eternal (Δ ⟨ ρ ⟩) x = ᴱ-eternal Δ x

-- A variable of a concatenation comes from one of the two parts.

∈-++ᶜ-split : ∀ {A ρ} → (Δ₁ Δ₂ : Ctx) → A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂)
            → (Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ₁) ⊎ (Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ₂)
∈-++ᶜ-split Δ₁ []         x        = inj₁ (_ , x)
∈-++ᶜ-split Δ₁ (Δ₂ ∷ B)   Hd       = inj₂ (_ , Hd)
∈-++ᶜ-split Δ₁ (Δ₂ ∷ B)   (Tl-∷ x) with ∈-++ᶜ-split Δ₁ Δ₂ x
... | inj₁ p        = inj₁ p
... | inj₂ (ρ' , y) = inj₂ (ρ' , Tl-∷ y)
∈-++ᶜ-split Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) with ∈-++ᶜ-split Δ₁ Δ₂ x
... | inj₁ p        = inj₁ p
... | inj₂ (ρ' , y) = inj₂ (ρ' ·ᵣ ρ , Tl-⟨⟩ y)

env-ᴱ : ∀ {St Γ} → (γ : Env St Γ) → ClosedVals (Γ ᴱ)

env-ᴱ ⌊ St ⌋ x =
  ⊥-elim (not-in-empty-ctx (subst (λ Γ' → _ ∈[ _ ] Γ') (toCtxᴱ-[] St) x))
env-ᴱ (γ ⟨ q ⟩ᵉ) x = env-ᴱ γ x
env-ᴱ (renᵉ {Γ₀ = Γ₀} γ r) x with ᴱ-eternal Γ₀ x | ∈-ᴱ⁻ Γ₀ x
... | et | ρ' , y with var-rename r y
... | ρ'' , _ , z = env-ᴱ γ (∈-ᴱ et z)
env-ᴱ (_∷ᵉ_ {A = A} γ V) x with eternal? A
env-ᴱ (_∷ᵉ_ {St = St} {A = A} γ V) Hd       | yes et =
  castᵛ (toCtxᴱ-[] St) (eternal-val-restrict et V)
env-ᴱ (_∷ᵉ_ γ V)                   (Tl-∷ y) | yes et = env-ᴱ γ y
env-ᴱ (_∷ᵉ_ γ V)                   x        | no ¬et = env-ᴱ γ x
env-ᴱ (eternalˡ {Γ = Γ} Δ lf η γ) x
  with ∈-++ᶜ-split (Δ ᴱ) (Γ ᴱ) (subst (λ Γ' → _ ∈[ _ ] Γ') (ᴱ-++ᶜ Δ Γ) x)
... | inj₁ (ρ' , y) = η (proj₂ (∈-ᴱ⁻ Δ y))
... | inj₂ (ρ' , y) = env-ᴱ γ y

------------------------------------------------------------------------
-- FUNCTORIALITY IN THE STATE
--
-- `BOX` steps `⟨St, box V M⟩ ↝ ⟨St ∷ₛ V', M⟩`, so the `box` case of the
-- fundamental lemma must move an environment to the extended state. The term
-- needs no reindexing — `toCtx (St ∷ₛ V) = toCtx St ∷ [ρ]A` is the context the
-- action already produced. The environment moves by structural recursion: a
-- weakening at the base, a longer slice at a lock.
------------------------------------------------------------------------

env-alloc : ∀ {St Γ A ρ} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
          → Env St Γ
          ---------------------
          → Env (St ∷ₛ V) Γ

env-alloc V ⌊ St ⌋            = renᵉ ⌊ St ∷ₛ V ⌋ wk-ren
env-alloc V (γ ⟨ q ⟩ᵉ)         = γ ⟨ slice-∘ (alloc-slice V) q ⟩ᵉ
env-alloc V (renᵉ γ r)        = renᵉ (env-alloc V γ) r
env-alloc V (γ ∷ᵉ W)          = (env-alloc V γ) ∷ᵉ slice-val (alloc-slice V) W
env-alloc V (eternalˡ Δ lf η γ) = eternalˡ Δ lf η (env-alloc V γ)

-- Allocation preserves reducibility of the environment, given that the new
-- cell is itself reducible (which is what `BOX` supplies). Each entry moves
-- along the allocation slice, so this is exactly `Val-slice`.

env-allocᴿ : ∀ {St Γ A ρ} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
           → (pV : Val A (St ⟨ ρ ⟩ₛ) (V-rename (eq-ren ++ᶜ-identityˡ) V))
           → (γ : Env St Γ) → Rel-Env γ
           ------------------------------
           → Rel-Env (env-alloc V γ)

env-allocᴿ V pV ⌊ St ⌋            pγ        = store-alloc V pγ pV
env-allocᴿ V pV (γ ⟨ q ⟩ᵉ)         pγ        = pγ
env-allocᴿ V pV (renᵉ γ r)        pγ        = env-allocᴿ V pV γ pγ
env-allocᴿ V pV (_∷ᵉ_ {A = A} γ W) (pγ , pW) =
  env-allocᴿ V pV γ pγ , Val-slice (alloc-slice V) W pW
env-allocᴿ V pV (eternalˡ Δ lf η γ) pγ      = env-allocᴿ V pV γ pγ
