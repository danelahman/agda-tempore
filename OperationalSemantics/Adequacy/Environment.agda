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
open import OperationalSemantics.Adequacy.RenEquivalence Spec
open import OperationalSemantics.Adequacy.Slice          Spec
open import OperationalSemantics.Adequacy.SubEquivalence Spec

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

ᴱ-lock-free : (Γ : Ctx) → Lock-free (Γ ᴱ)
ᴱ-lock-free []        = lf-[]
ᴱ-lock-free (Γ ∷ A)   with eternal? A
... | yes _           = lf-∷ (ᴱ-lock-free Γ)
... | no  _           = ᴱ-lock-free Γ
ᴱ-lock-free (Γ ⟨ ρ ⟩) = ᴱ-lock-free Γ

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

  -- precomposition with a renaming: what makes `Env` functorial in the
  -- state (`env-alloc`). Kept separate from `⌊_⌋` so that the identity
  -- case of the action stays `refl`, `Ren` being unquotiented.

  renᵉ     : ∀ {St Γ Γ₀}
           → Env St Γ → Ren [] Γ₀ Γ
           ---------------------
           → Env St Γ₀

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
Rel-Env (renᵉ γ r)             = Rel-Env γ
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
Eternal-Env (renᵉ γ r)          = Eternal-Env γ
Eternal-Env (sliceᵉ γ q)        = Eternal-Env γ
Eternal-Env (γ ⟨ q ⟩ᵉ)           = Eternal-Env γ
Eternal-Env (γ ∷ᵉ V)            = Eternal-Env γ
Eternal-Env (liftᵉ V γ)         = Eternal-Env γ
Eternal-Env (eternalˡ Δ lf η γ) =
  Eternal-Env γ × (∀ {A ρ} → A ∈[ ρ ] Δ → Eternal A)

Rel-Env-eternal : ∀ {St Γ} → (γ : Env St Γ) → Rel-Env γ → Eternal-Env γ
Rel-Env-eternal ⌊ St ⌋              pγ        = tt
Rel-Env-eternal (∅ᵉ St)              pγ        = tt
Rel-Env-eternal (renᵉ γ r)          pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (sliceᵉ γ q)        pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (γ ⟨ q ⟩ᵉ)           pγ        = Rel-Env-eternal γ pγ
Rel-Env-eternal (γ ∷ᵉ V)            (pγ , _)  = Rel-Env-eternal γ pγ
Rel-Env-eternal (liftᵉ V γ)         (pγ , _)  = Rel-Env-eternal γ pγ
Rel-Env-eternal (eternalˡ Δ lf η γ) (pγ , et) = Rel-Env-eternal γ pγ , et

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

cast-lam : ∀ {Γ Γ' A C} → (e : Γ ≡ Γ') → (M : Γ ∷ A ⊢C⦂ C)
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

cast-handle : ∀ {Γ Γ' A B ε ε'} → (e : Γ ≡ Γ')
            → {M : Γ ⊢C⦂ A ‼ ε}
            → {H : (op : Op) → (ε'' : E) →
                     Γ ᴱ ∷ type-of-gtype (param op)
                       ∷ [ mapᵉ (op-grade op) ]
                           (type-of-gtype (arity op) ⇒ B ‼ ε'')
                     ⊢C⦂ B ‼ (op-grade op ·ₑ ε'')}
            → {N : Γ ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B ‼ ε'}
            → castᶜ e (handle M `with H `in N)
            ≡ handle (castᶜ e M)
              `with (λ op ε'' →
                       castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                                             ∷ [ mapᵉ (op-grade op) ]
                                                 (type-of-gtype (arity op) ⇒ B ‼ ε''))
                              e)
                             (H op ε''))
              `in (castᶜ (cong (λ Γ₁ → Γ₁ ⟨ mapᵉ ε ⟩ ∷ A) e) N)
cast-handle refl = refl

-- SUBSTITUTION RESPECTS A CONTEXT TRANSPORT
--
-- Relocating a term's context relocates the variable it is substituted at, and
-- the replacement's own context along with it. All four hold by matching the
-- equality, but they are what lets a substitution be moved across the
-- `ᴱ`/`++ᶜ` transports that `handle`'s eternal clause accumulates.

split-l-cast : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
             → split-l x ≡ split-l (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
split-l-cast refl x = refl

split-r-cast : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
             → split-r x ≡ split-r (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
split-r-cast refl x = refl

sub-cast-C : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C) → (x : A ∈[ ρ ] Γ)
           → (W : split-l x ⊢V⦂ A)
           → subst (_⊢C⦂ C) (cong₂ _++ᶜ_ (split-l-cast e x) (split-r-cast e x))
               (M [ x ↦ W ]c)
           ≡ (subst (_⊢C⦂ C) e M)
               [ subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
               ↦ subst (_⊢V⦂ A) (split-l-cast e x) W ]c
sub-cast-C refl M x W = refl

sub-cast-V : ∀ {Γ Γ' A B ρ} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ B) → (x : A ∈[ ρ ] Γ)
           → (W : split-l x ⊢V⦂ A)
           → subst (_⊢V⦂ B) (cong₂ _++ᶜ_ (split-l-cast e x) (split-r-cast e x))
               (V [ x ↦ W ]v)
           ≡ (subst (_⊢V⦂ B) e V)
               [ subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
               ↦ subst (_⊢V⦂ A) (split-l-cast e x) W ]v
sub-cast-V refl V x W = refl

-- The same, packaged for a caller that knows where the transport sends the
-- substituted variable and what value it carries there. Both equations are
-- matched, so the two substitutions are literally the same one.

sub-cast-C′ : ∀ {Γ Γ' A C ρ} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
            → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ ] Γ')
            → (ey : subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x ≡ y)
            → (U : split-l x ⊢V⦂ A) → (U' : split-l y ⊢V⦂ A)
            → subst (_⊢V⦂ A) (trans (split-l-cast e x) (cong split-l ey)) U ≡ U'
            → (subst (_⊢C⦂ C) e M) [ y ↦ U' ]c
            ≡ subst (_⊢C⦂ C)
                (cong₂ _++ᶜ_ (trans (split-l-cast e x) (cong split-l ey))
                             (trans (split-r-cast e x) (cong split-r ey)))
                (M [ x ↦ U ]c)
sub-cast-C′ refl M x .x refl U .U refl = refl

-- Transports along context equalities, all normalised to `subst` so that a
-- chain of them fuses and collapses by `uip`.

castᶜ≡subst : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → (M : Γ ⊢C⦂ C)
            → castᶜ e M ≡ subst (_⊢C⦂ C) e M
castᶜ≡subst refl M = refl

subst-++ᶜʳ : ∀ {Γ Γ' C} → (D : Ctx) → (e : Γ ≡ Γ') → (M : (Γ ++ᶜ D) ⊢C⦂ C)
           → subst (λ Γ₀ → (Γ₀ ++ᶜ D) ⊢C⦂ C) e M
           ≡ subst (_⊢C⦂ C) (cong (_++ᶜ D) e) M
subst-++ᶜʳ D refl M = refl

-- Three transports whose composite is a loop are the identity.

subst-loop₃ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e₁ : Γ₁ ≡ Γ₂) → (e₂ : Γ₂ ≡ Γ₃) → (e₃ : Γ₃ ≡ Γ₁)
            → (M : Γ₁ ⊢C⦂ C)
            → subst (_⊢C⦂ C) e₃ (subst (_⊢C⦂ C) e₂ (subst (_⊢C⦂ C) e₁ M)) ≡ M
subst-loop₃ refl refl e₃ M =
  cong (λ z → subst (_⊢C⦂ _) z M) (uip {p = e₃} {q = refl})

-- Two transports fuse into one; a transport that returns to its own context is
-- the identity. Together they collapse a tower of any height.

subst-fuseᶜ : ∀ {Γ₁ Γ₂ Γ₃ C} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (M : Γ₁ ⊢C⦂ C)
            → subst (_⊢C⦂ C) e' (subst (_⊢C⦂ C) e M)
            ≡ subst (_⊢C⦂ C) (trans e e') M
subst-fuseᶜ refl refl M = refl

subst-loopᶜ : ∀ {Γ C} → (e : Γ ≡ Γ) → (M : Γ ⊢C⦂ C) → subst (_⊢C⦂ C) e M ≡ M
subst-loopᶜ {C = C} e M = cong (λ z → subst (_⊢C⦂ C) z M) (uip {p = e} {q = refl})

subst-subst-sym′ : ∀ {a p} {X : Set a} {P : X → Set p} {u v : X}
                 → (e : u ≡ v) → (w : P v)
                 → subst P e (subst P (sym e) w) ≡ w
subst-subst-sym′ refl w = refl

-- Relocating a weakening's two contexts. Renaming algebra, so it belongs
-- upstream with `_≐ʳ_` (see the cleanup list); it is here because nothing else
-- uses it yet. With both equalities matched the conjugating renamings are
-- identity-like, and any two proofs of the (only propositional) context
-- equations agree by `uip`.

cong-ren-wk-cast-≐ : ∀ {B} → (Γ₀ Γ₁ Θ₀ Θ₁ : Ctx) → Γ₀ ≡ Γ₁ → Θ₀ ≡ Θ₁
                   → (e  : Γ₁ ++ᶜ Θ₁ ≡ Γ₀ ++ᶜ Θ₀)
                   → (e' : (Γ₀ ∷ B) ++ᶜ Θ₀ ≡ (Γ₁ ∷ B) ++ᶜ Θ₁)
                   → cong-ren {Γ'' = Θ₁} (wk-ren {A = B})
                   ≐ʳ (eq-ren e' ∘ʳ cong-ren {Γ'' = Θ₀} (wk-ren {A = B})
                                 ∘ʳ eq-ren e)
cong-ren-wk-cast-≐ {B} Γ₀ Γ₁ Θ₀ Θ₁ refl refl e e' =
  ≐ʳ-sym
    (≐ʳ-trans (∘ʳ-≐ (eq-ren-≐ e' refl)
                    (∘ʳ-≐ ≐ʳ-refl (eq-ren-≐ e refl)))
              (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _)))

castʳᵉ : ∀ {Γ Γ' Δ ρ} → Γ ≡ Γ' → Ren [] (Δ ⟨ ρ ⟩) Γ → Ren [] (Δ ⟨ ρ ⟩) Γ'
castʳᵉ refl w = w

cast-unbox : ∀ {Γ Γ' A C ρ Δ} → (e : Γ ≡ Γ')
           → {w : Ren [] (Δ ⟨ ρ ⟩) Γ} → {V : Δ ⊢V⦂ [ ρ ] A} → {M : Γ ∷ A ⊢C⦂ C}
           → castᶜ e (unbox w V M)
           ≡ unbox (castʳᵉ e w) V (castᶜ (cong (_∷ A) e) M)
cast-unbox refl = refl

-- A cast does not move the cell an `unbox` names.

unbox-tgt-castʳᵉ : ∀ {Γ Γ' A ρ Δ} → (e : Γ ≡ Γ') → (w : Ren [] (Δ ⟨ ρ ⟩) Γ)
                 → (V : Δ ⊢V⦂ [ ρ ] A)
                 → unbox-tgt (castʳᵉ e w) V
                 ≡ (proj₁ (unbox-tgt w V)
                   , subst (λ Γ₀ → [ ρ ] A ∈[ proj₁ (unbox-tgt w V) ] Γ₀) e
                           (proj₂ (unbox-tgt w V)))
unbox-tgt-castʳᵉ refl w V = refl

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
env-Vˢ (∅ᵉ St) Δ V = V-rename (cong-ren (∅-ren St)) V
env-Vˢ (renᵉ γ r) Δ V = env-Vˢ γ Δ (V-rename (cong-ren r) V)
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
env-Cˢ (renᵉ γ r) Δ M = env-Cˢ γ Δ (C-rename (cong-ren r) M)
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
env-Vˢ-lam (renᵉ γ r) Δ M = env-Vˢ-lam γ Δ _
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
env-Cˢ-ret (renᵉ γ r) Δ V = env-Cˢ-ret γ Δ _
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
env-Cˢ-app (renᵉ γ r) Δ V U = env-Cˢ-app γ Δ _ _
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
env-Cˢ-absurd (renᵉ γ r) Δ V = env-Cˢ-absurd γ Δ _
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
env-Cˢ-coerce (renᵉ γ r) Δ M = env-Cˢ-coerce γ Δ _
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
env-Vˢ-pair (renᵉ γ r) Δ V U = env-Vˢ-pair γ Δ _ _
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
env-Vˢ-const (renᵉ γ r) Δ c = env-Vˢ-const γ Δ _
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
env-Vˢ-⋆ (renᵉ γ r) Δ  = env-Vˢ-⋆ γ Δ
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
env-Cˢ-delay (renᵉ γ r) Δ M = env-Cˢ-delay γ Δ _
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
env-Cˢ-seq (renᵉ γ r) Δ M N = env-Cˢ-seq γ Δ _ _
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
env-Cˢ-perform (renᵉ γ r) Δ V M = env-Cˢ-perform γ Δ _ _
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
env-Cˢ-match (renᵉ γ r) Δ V M = env-Cˢ-match γ Δ _ _
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
env-Cˢ-box (renᵉ γ r) Δ V M = env-Cˢ-box γ Δ _ _
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

Fam : VType → Ctx → Set
Fam B Γ₀ = (op : Op) → (ε : E) → Cl B op ε Γ₀

-- Relocating a clause along an equality of the context it restricts. Written in
-- exactly the shape `cast-handle` produces, so that the two agree on the nose
-- and no `castᶜ-irr` is needed at any use site.

Cl-cast : ∀ {Γ Γ' B} → (op : Op) → (ε : E) → Γ ≡ Γ'
        → Cl B op ε (Γ ᴱ) → Cl B op ε (Γ' ᴱ)
Cl-cast {B = B} op ε e X =
  castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                        ∷ [ mapᵉ (op-grade op) ]
                            (type-of-gtype (arity op) ⇒ B ‼ ε))
              e)
        X

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

env-Hˢ (renᵉ γ r) Δ K =
  env-Hˢ γ Δ (λ op ε →
    C-rename (cong-∷-ren (cong-∷-ren
               (restrict-ren (cong-ren {Γ'' = Δ} r)))) (K op ε))

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
env-Cˢ-handle (renᵉ γ r) Δ M H N = env-Cˢ-handle γ Δ _ _ _
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
-- (`∈-ᴱ⁻`, in `RenEquivalence`), and every variable of the eternal restriction has eternal type.

ᴱ-eternal : ∀ {A ρ} → (Δ : Ctx) → A ∈[ ρ ] Δ ᴱ → Eternal A
ᴱ-eternal []        x with x
... | ()
ᴱ-eternal (Δ ∷ B)   x with eternal? B
ᴱ-eternal (Δ ∷ B)   Hd       | yes et = et
ᴱ-eternal (Δ ∷ B)   (Tl-∷ y) | yes _  = ᴱ-eternal Δ y
ᴱ-eternal (Δ ∷ B)   x        | no  _  = ᴱ-eternal Δ x
ᴱ-eternal (Δ ⟨ ρ ⟩) x = ᴱ-eternal Δ x

-- A variable of a concatenation comes from one of the two parts.

-- The grade of a variable of the *right* part is unchanged: only that part's
-- locks stand to its right.

∈-++ᶜ-split : ∀ {A ρ} → (Δ₁ Δ₂ : Ctx) → A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂)
            → (Σ[ ρ' ∈ R ] A ∈[ ρ' ] Δ₁) ⊎ (A ∈[ ρ ] Δ₂)
∈-++ᶜ-split Δ₁ []         x        = inj₁ (_ , x)
∈-++ᶜ-split Δ₁ (Δ₂ ∷ B)   Hd       = inj₂ Hd
∈-++ᶜ-split Δ₁ (Δ₂ ∷ B)   (Tl-∷ x) with ∈-++ᶜ-split Δ₁ Δ₂ x
... | inj₁ p = inj₁ p
... | inj₂ y = inj₂ (Tl-∷ y)
∈-++ᶜ-split Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) with ∈-++ᶜ-split Δ₁ Δ₂ x
... | inj₁ p = inj₁ p
... | inj₂ y = inj₂ (Tl-⟨⟩ y)

env-ᴱ : ∀ {St Γ} → (γ : Env St Γ) → ClosedVals (Γ ᴱ)

env-ᴱ ⌊ St ⌋ x =
  ⊥-elim (not-in-empty-ctx (subst (λ Γ' → _ ∈[ _ ] Γ') (toCtxᴱ-[] St) x))
env-ᴱ (∅ᵉ St) x = ⊥-elim (not-in-empty-ctx x)
-- a cell's type is a box type, never eternal, so the prefix is unchanged
env-ᴱ (liftᵉ {A = A} {ρ = ρ} V γ) x with eternal? ([ ρ ] A)
... | yes ()
... | no ¬et = env-ᴱ γ x
env-ᴱ (γ ⟨ q ⟩ᵉ) x = env-ᴱ γ x
env-ᴱ (sliceᵉ γ q) x = env-ᴱ γ x
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
-- Proving it needs a lemma the development does not yet have: *renaming
-- commutes with substitution* — `C-rename (cong-ren r) (M [ x ↦ V ]c) ≐ᶜ
-- (C-rename (cong-ren r) M) [ x ↦ V-rename r V ]c` at an arbitrary suffix. The
-- `_∷ᵉ_` zone is where it bites: `env-Hˢ` substitutes there *after* the zones to
-- its left have run, `env-eternal-C` *before*. That lemma is a mutual induction
-- on the term of `sub-wk`'s size, and `FL-match` wants its substitution/
-- substitution counterpart.

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

postulate
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

castᶜ-≐ : ∀ {Γ Γ' C} → (e : Γ ≡ Γ') → {M M' : Γ ⊢C⦂ C}
        → M ≐ᶜ M' → castᶜ e M ≐ᶜ castᶜ e M'
castᶜ-≐ refl eM = eM

castᵛ-≐ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {V V' : Γ ⊢V⦂ A}
        → V ≐ᵛ V' → castᵛ e V ≐ᵛ castᵛ e V'
castᵛ-≐ refl eV = eV

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
env-Vˢ-≐ (renᵉ γ r)   Δ eV = env-Vˢ-≐ γ Δ (V-rename-cong (cong-ren r) eV)
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

------------------------------------------------------------------------
-- SUFFIX VARIABLES
--
-- The action is defined under a suffix `Δ`, and a variable of that suffix is
-- one the environment does not close: it is carried along, its position fixed
-- and only its grade bound recomputed. `∈-++ᶜʳ` is the injection, and the
-- lemmas below are what the recursion needs to see through the casts and the
-- congruence renamings.
------------------------------------------------------------------------

-- A cast acts on a variable by relocating it.

castᵛ-var : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ')
          → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (x : A ∈[ ρ ] Γ)
          → castᵛ e (var f x) ≡ var f (subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x)
castᵛ-var refl f x = refl

-- The same, taking the relocation as a `Tgt` equality — which is what the
-- pushing lemmas below have, their grades changing along with their positions.

castᵛ-var-Tgt : ∀ {Γ Γ' A ρ ρ'} → (e : Γ ≡ Γ')
              → (x : A ∈[ ρ ] Γ) → (x' : A ∈[ ρ' ] Γ')
              → Tgt-cast e (ρ , x) ≡ (ρ' , x')
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (f' : ¬ Eternal A → ρ' ≾ᵣ uᵣ)
              → castᵛ e (var f x) ≐ᵛ var f' x'
castᵛ-var-Tgt refl x _ refl f f' = var-≐

-- A cast cancels its own inverse.

castᵛ-sym-cast : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ' ⊢V⦂ A)
               → castᵛ e (castᵛ (sym e) V) ≡ V
castᵛ-sym-cast refl V = refl

-- Casting the target of a renaming is prefixing it with an `eq-ren`.

castᵛ-rename : ∀ {Γ Γ' Γ'' A} → (e : Γ' ≡ Γ'') → (r : Ren [] Γ Γ')
             → (V : Γ ⊢V⦂ A)
             → castᵛ e (V-rename r V) ≐ᵛ V-rename (eq-ren e ∘ʳ r) V
castᵛ-rename refl r V =
  ≐ᵛ-sym (≐ᵛ-trans (V-rename-∘ id-ren r V) (V-rename-id-≐ ≐ʳ-refl _))

-- Relocating a suffix variable along associativity re-brackets the injection.

∈-++ᶜʳ-assoc : ∀ {A ρ} → (Γ Γ' : Ctx) → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
             → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) (++ᶜ-assoc Γ Γ' Δ)
                     (∈-++ᶜʳ {Γ = Γ ++ᶜ Γ'} x)
             ≡ ∈-++ᶜʳ {Γ = Γ} (∈-++ᶜʳ {Γ = Γ'} x)

∈-++ᶜʳ-assoc Γ Γ' {Δ ∷ B} Hd       = subst-Hd (++ᶜ-assoc Γ Γ' Δ)
∈-++ᶜʳ-assoc Γ Γ' {Δ ∷ B} (Tl-∷ x) =
  trans (subst-Tl-∷ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))
        (cong Tl-∷ (∈-++ᶜʳ-assoc Γ Γ' x))
∈-++ᶜʳ-assoc Γ Γ' {Δ ⟨ ρ ⟩} (Tl-⟨⟩ x) =
  trans (subst-Tl-⟨⟩ (++ᶜ-assoc Γ Γ' Δ) (∈-++ᶜʳ x))
        (cong Tl-⟨⟩ (∈-++ᶜʳ-assoc Γ Γ' x))

-- A congruence renaming fixes a suffix variable, up to its grade bound.

cong-ren-tgt-r : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
               → var-tgt (cong-ren {Γ'' = Δ} r) (∈-++ᶜʳ {Γ = Γ} x)
               ≡ (ρ , ∈-++ᶜʳ {Γ = Γ'} x)

cong-ren-tgt-r r Hd        = refl
cong-ren-tgt-r r (Tl-∷ x)  =
  cong (λ z → proj₁ z , Tl-∷ (proj₂ z)) (cong-ren-tgt-r r x)
cong-ren-tgt-r r (Tl-⟨⟩ {ρ = ρ₁} x) =
  cong (λ z → proj₁ z ·ᵣ ρ₁ , Tl-⟨⟩ (proj₂ z)) (cong-ren-tgt-r r x)

-- Renaming a suffix variable along a congruence renaming leaves it where it is.

ren-var-r : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → {Δ : Ctx} → (x : A ∈[ ρ ] Δ)
          → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → V-rename (cong-ren {Γ'' = Δ} r) (var f (∈-++ᶜʳ {Γ = Γ} x))
          ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ'} x)
ren-var-r r x f f' =
  var-ren-tgt-≐ (cong-ren r) (∈-++ᶜʳ x) f (cong-ren-tgt-r r x) f'

-- SUBSTITUTION FIXES A SUFFIX VARIABLE
--
-- The variable being replaced lies in the prefix, so a suffix variable survives
-- it: what comes back is that variable again, its position fixed and only its
-- grade bound recomputed. Induction on the suffix variable, which is also the
-- recursion of `split-≡-++ᶜ = ≡-split refl` and of `⟨_,_⟩[_↦_]var`.

≡→≐ᵛ : ∀ {Γ A} {V V' : Γ ⊢V⦂ A} → V ≡ V' → V ≐ᵛ V'
≡→≐ᵛ refl = ≐ᵛ-refl _

-- Relocating a variable along an equality of *extended* contexts: the equality
-- must have come from one of the smaller contexts, and any two proofs agree.

-- Relocating a variable along a proof that its context is what it is.

subst-var-id : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
             → subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
             ≡ subst (λ Γ₀ → A ∈[ ρ ] Γ₀) e x
subst-var-id e x = refl

subst-Hd-any : ∀ {Γ Γ' A} → (e : Γ ∷ A ≡ Γ' ∷ A)
             → subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) e Hd ≡ Hd
subst-Hd-any {A = A} e =
  trans (cong (λ z → subst (λ Γ₀ → A ∈[ uᵣ ] Γ₀) z Hd)
              (uip {p = e} {q = cong (_∷ A) (∷ᶜ-injective-ctx e)}))
        (subst-Hd (∷ᶜ-injective-ctx e))

-- A cast commutes with the three things the substitution puts in front of the
-- recursive call: a weakening, an eternal extension, and a lock-crossing
-- renaming. Each is uniform in its context, so matching the equality suffices.

cast-wk-any : ∀ {Γ Γ' A C} → (e : Γ ∷ C ≡ Γ' ∷ C) → (e₀ : Γ ≡ Γ')
            → (V : Γ ⊢V⦂ A)
            → castᵛ e (V-rename (wk-ren {A = C}) V)
            ≡ V-rename wk-ren (castᵛ e₀ V)
cast-wk-any refl e₀ V rewrite uip {p = e₀} {q = refl} = refl

cast-ext-any : ∀ {Γ Γ' A ρ} → (e : Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ ⟩) → (e₀ : Γ ≡ Γ')
             → (et : Eternal A) → (V : Γ ⊢V⦂ A)
             → castᵛ e (eternal-val-ext {ρ = ρ} et V)
             ≡ eternal-val-ext et (castᵛ e₀ V)
cast-ext-any refl e₀ et V rewrite uip {p = e₀} {q = refl} = refl

cast-ren-⟨⟩-any : ∀ {Γ Γ' A ρ} → (e : Γ ⟨ ρ ⟩ ≡ Γ' ⟨ ρ ⟩) → (e₀ : Γ ≡ Γ')
                → (r : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)) → (V : Γ ⊢V⦂ A)
                → castᵛ e (V-rename r V) ≡ V-rename r (castᵛ e₀ V)
cast-ren-⟨⟩-any refl e₀ r V rewrite uip {p = e₀} {q = refl} = refl

-- The context equality the substitution's result is presented along.

castOf : ∀ {Γ₁ B} → (Γ₂ : Ctx)
       → (split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
            ++ᶜ split-r (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})))
       ≡ (Γ₁ ++ᶜ Γ₂)
castOf {Γ₁} {B} Γ₂ =
  cong₂ _++ᶜ_ (split→∈-split-l (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
              (split→∈-split-r (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))

sub-var-r : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ∀ {A ρ}
          → (x : A ∈[ ρ ] Γ₂)
          → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
          → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          → castᵛ (castOf {Γ₁} {B} Γ₂)
              (⟨ ∈-++ᶜʳ {Γ = Γ₁ ∷ B} x , f ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})
                                            ↦ W ]var)
          ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ₁} x)

sub-var-r {Γ₁} {B} (Γ₂ ∷ C) Hd W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (trans (castᵛ-var (castOf {Γ₁} {B} (Γ₂ ∷ C)) f Hd)
                 (cong (var f) (subst-Hd-any (castOf {Γ₁} {B} (Γ₂ ∷ C))))))
    var-≐

sub-var-r {Γ₁} {B} (Γ₂ ∷ C) (Tl-∷ x) W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any (castOf {Γ₁} {B} (Γ₂ ∷ C)) (castOf {Γ₁} {B} Γ₂) _))
    (≐ᵛ-trans (V-rename-cong wk-ren (sub-var-r Γ₂ x W f f))
              (var-ren-tgt-≐ wk-ren (∈-++ᶜʳ {Γ = Γ₁} x) f refl f'))

sub-var-r {Γ₁} {B} (Γ₂ ⟨ ρ ⟩) {A = A} (Tl-⟨⟩ x) W f f' with eternal? A

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ext-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ ⟩)) (castOf {Γ₁} {B} Γ₂) et _))
    (≐ᵛ-trans (eternal-val-ext-cong et
                (sub-var-r Γ₂ x W _ (λ z → ⊥-elim (z et)))) var-≐)

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ ⟩)) (castOf {Γ₁} {B} Γ₂) rn _))
    (≐ᵛ-trans (V-rename-cong rn (sub-var-r Γ₂ x W fᵢ fᵢ))
              (var-ren-tgt-≐ rn (∈-++ᶜʳ {Γ = Γ₁} x) fᵢ
                 (cong (var-tgt′ (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et))))
                       (⟨⟩-η⁻¹-tgt (∈-++ᶜʳ {Γ = Γ₁} x)))
                 f'))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

    fᵢ = λ z → ≾ᵣ-zero-productˡ (f z)

-- A variable the splitting sends right *is* that variable, pushed right.

∈-++ᶜ-split-inj₂ : ∀ {A ρ} → (Δ₁ Δ₂ : Ctx) → (x : A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂))
                 → (y : A ∈[ ρ ] Δ₂)
                 → ∈-++ᶜ-split Δ₁ Δ₂ x ≡ inj₂ y
                 → x ≡ ∈-++ᶜʳ {Γ = Δ₁} y

∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ∷ B) Hd .Hd refl = refl

∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) y eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₁ p  with eq
...   | ()
∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) y eq
    | inj₂ y' with eq
...   | refl = cong Tl-∷ (∈-++ᶜ-split-inj₂ Δ₁ Δ₂ x y' eq')

∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) y eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₁ p  with eq
...   | ()
∈-++ᶜ-split-inj₂ Δ₁ (Δ₂ ⟨ ρ ⟩) (Tl-⟨⟩ x) y eq
    | inj₂ y' with eq
...   | refl = cong Tl-⟨⟩ (∈-++ᶜ-split-inj₂ Δ₁ Δ₂ x y' eq')

-- A variable the splitting sends left is that variable pushed under the suffix.
-- Stated as a `Tgt` equality, so the grade travels with the position.

∈-++ᶜ-split-inj₁ : ∀ {A ρ ρ'} → (Δ₁ Δ₂ : Ctx) → (x : A ∈[ ρ ] (Δ₁ ++ᶜ Δ₂))
                 → (z : A ∈[ ρ' ] Δ₁)
                 → ∈-++ᶜ-split Δ₁ Δ₂ x ≡ inj₁ (ρ' , z)
                 → (ρ , x) ≡ (grade-++ᶜˡ ρ' Δ₂ , ∈-++ᶜˡ Δ₂ z)

∈-++ᶜ-split-inj₁ Δ₁ []       x .x refl = refl

∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ∷ B) Hd       z eq with eq
... | ()
∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) z eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₂ _  with eq
...   | ()
∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ∷ B) (Tl-∷ x) z eq
    | inj₁ (ρ'' , z') with eq
...   | refl =
  cong (λ t → proj₁ t , Tl-∷ (proj₂ t)) (∈-++ᶜ-split-inj₁ Δ₁ Δ₂ x z' eq')

∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ⟨ ρ₁ ⟩) (Tl-⟨⟩ x) z eq
  with ∈-++ᶜ-split Δ₁ Δ₂ x in eq'
... | inj₂ _  with eq
...   | ()
∈-++ᶜ-split-inj₁ Δ₁ (Δ₂ ⟨ ρ₁ ⟩) (Tl-⟨⟩ x) z eq
    | inj₁ (ρ'' , z') with eq
...   | refl =
  cong (λ t → proj₁ t ·ᵣ ρ₁ , Tl-⟨⟩ (proj₂ t))
       (∈-++ᶜ-split-inj₁ Δ₁ Δ₂ x z' eq')

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

-- SUBSTITUTION FIXES A PREFIX VARIABLE
--
-- The mirror of `sub-var-r`: the variable being replaced is the `B` sitting at
-- the boundary, so a variable of the prefix survives it too, landing at the
-- corresponding position of the shorter prefix. Same induction on the suffix.

sub-var-l : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ∀ {A ρ}
          → (x : A ∈[ ρ ] Γ₁)
          → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
          → (f  : ¬ Eternal A → grade-++ᶜˡ ρ Γ₂ ≾ᵣ uᵣ)
          → (f' : ¬ Eternal A → grade-++ᶜˡ ρ Γ₂ ≾ᵣ uᵣ)
          → castᵛ (castOf {Γ₁} {B} Γ₂)
              (⟨ ∈-++ᶜˡ {Γ = Γ₁ ∷ B} Γ₂ (Tl-∷ x) , f
               ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) ↦ W ]var)
          ≐ᵛ var f' (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x)

sub-var-l {Γ₁} {B} [] x W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (trans (castᵛ-var (castOf {Γ₁} {B} []) f x)
                 (cong (var f) (subst-var-id (castOf {Γ₁} {B} []) x))))
    var-≐

sub-var-l {Γ₁} {B} (Γ₂ ∷ C) x W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any (castOf {Γ₁} {B} (Γ₂ ∷ C)) (castOf {Γ₁} {B} Γ₂) _))
    (≐ᵛ-trans (V-rename-cong wk-ren (sub-var-l Γ₂ x W f f))
              (var-ren-tgt-≐ wk-ren (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x) f refl f'))

sub-var-l {Γ₁} {B} (Γ₂ ⟨ ρ' ⟩) {A = A} x W f f' with eternal? A

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ext-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ' ⟩)) (castOf {Γ₁} {B} Γ₂) et _))
    (≐ᵛ-trans (eternal-val-ext-cong et
                (sub-var-l Γ₂ x W _ (λ z → ⊥-elim (z et)))) var-≐)

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ' ⟩))
                           (castOf {Γ₁} {B} Γ₂) rn _))
    (≐ᵛ-trans (V-rename-cong rn (sub-var-l Γ₂ x W fᵢ fᵢ))
              (var-ren-tgt-≐ rn (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x) fᵢ
                 (cong (var-tgt′ (⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et))))
                       (⟨⟩-η⁻¹-tgt (∈-++ᶜˡ {Γ = Γ₁} Γ₂ x)))
                 f'))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ' ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

    fᵢ = λ z → ≾ᵣ-zero-productˡ (f z)

-- SUBSTITUTION AT THE VARIABLE IT REPLACES
--
-- The third possibility: the variable looked up *is* the one being replaced, so
-- what comes back is the value, pushed under the suffix. The recursion of
-- `⟨_,_⟩[_↦_]var` builds that push one layer at a time — `wk-ren` per binder and
-- `⟨⟩-≤-ren ∘ʳ ⟨⟩-η⁻¹-ren` per lock — which is exactly `push-ren`, up to the
-- grade bounds `_≐ʳ_` does not see. Non-eternality is what selects that branch
-- at a lock; at an eternal type the substitution extends the value instead.

sub-var-hit : ∀ {Γ₁ B} → (Γ₂ : Ctx) → ¬ Eternal B
            → (p : ctx-grade Γ₂ ≾ᵣ uᵣ)
            → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
            → (f : ¬ Eternal B → ctx-grade Γ₂ ≾ᵣ uᵣ)
            → castᵛ (castOf {Γ₁} {B} Γ₂)
                (⟨ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) , f
                 ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) ↦ W ]var)
            ≐ᵛ V-rename (push-ren Γ₂ p)
                 (castᵛ (split→∈-split-l (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) W)

sub-var-hit {Γ₁} {B} [] ¬et p W f =
  ≐ᵛ-sym (V-rename-id-≐ ≐ʳ-refl _)

sub-var-hit {Γ₁} {B} (Γ₂ ∷ C) ¬et p W f =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any (castOf {Γ₁} {B} (Γ₂ ∷ C)) (castOf {Γ₁} {B} Γ₂) _))
    (≐ᵛ-trans (V-rename-cong wk-ren (sub-var-hit Γ₂ ¬et p W f))
              (≐ᵛ-sym (V-rename-∘ wk-ren (push-ren Γ₂ p) _)))

sub-var-hit {Γ₁} {B} (Γ₂ ⟨ ρ ⟩) ¬et p W f with eternal? B

... | yes et = ⊥-elim (¬et et)

... | no ¬p =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any (castOf {Γ₁} {B} (Γ₂ ⟨ ρ ⟩))
                           (castOf {Γ₁} {B} Γ₂) rn _))
    (≐ᵛ-trans (V-rename-cong rn (sub-var-hit Γ₂ ¬et pᵢ W fᵢ))
      (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ rn (push-ren Γ₂ pᵢ) _))
                (V-rename-≐ (∘ʳ-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl) ≐ʳ-refl) _)))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f ¬p)) ∘ʳ ⟨⟩-η⁻¹-ren

    pᵢ = ≾ᵣ-zero-productˡ p
    fᵢ = λ z → ≾ᵣ-zero-productˡ (f z)

-- The same, taking the looked-up variable as an equation: what reaches the
-- substitution is `∈-++ᶜˡ Γ₂ Hd`, which is `split→∈` of the splitting only up
-- to `split→∈-∈-++ᶜˡ`.

sub-var-hit′ : ∀ {Γ₁ B σ} → (Γ₂ : Ctx) → ¬ Eternal B
             → (p : ctx-grade Γ₂ ≾ᵣ uᵣ)
             → (y : B ∈[ σ ] ((Γ₁ ∷ B) ++ᶜ Γ₂))
             → _≡_ {A = Tgt ((Γ₁ ∷ B) ++ᶜ Γ₂) B}
                 (σ , y)
                 (ctx-grade Γ₂ , split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}))
             → (W : split-l (split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) ⊢V⦂ B)
             → (f : ¬ Eternal B → σ ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ₁} {B} Γ₂)
                 (⟨ y , f ⟩[ split→∈ (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂}) ↦ W ]var)
             ≐ᵛ V-rename (push-ren Γ₂ p)
                  (castᵛ (split→∈-split-l (split-≡-++ᶜ {Γ₁ ∷ B} {Γ₂})) W)
sub-var-hit′ Γ₂ ¬et p _ refl W f = sub-var-hit Γ₂ ¬et p W f

-- THE CELL `unbox-var` NAMES (what `sub-wk-unbox` needs)
--
-- `unbox-var z rel M` rebuilds an unboxing whose boxed value is the head
-- variable of `split-l z ∷ [ ρ ] A`, so the cell it names is `z` itself — the
-- syntactic counterpart of `split-lookup` in
-- `Interpretation.SubstitutionCoherence`. Its renaming is
-- `eq-ren (split-≡ (split-pf z)) ∘ʳ wk-ren-⟨ρ⟩-ctx (split-grade-≡ z) ∘ʳ ⟨⟩-≤-ren rel`,
-- so computing its `var-tgt` at `Tl-⟨⟩ Hd` needs, in order: `⟨⟩-≤-ren`'s clause,
-- `wk-ren-⟨ρ⟩-ctx-tgt` (in `Slice`, proved), and `eq-ren-tgt` below. What is left
-- is
--
--   split-lookup-tgt : (z : [ ρ ] A ∈[ ρ' ] Γ)
--                    → (grade-++ᶜˡ uᵣ (split-r z)
--                      , subst _ (split-≡ (split-pf z))
--                              (∈-++ᶜˡ (split-r z) (Hd {Γ = split-l z})))
--                    ≡ (ρ' , z)
--
-- by induction on `z` — `Hd` is `refl`, and the two `Tl` cases are `subst-Tl-∷`
-- resp. `subst-Tl-⟨⟩` under a `cong`. **State it with `∈-++ᶜˡ`, not
-- `var-ρ-++ᶜ`**: the latter carries a grade `subst` in each of its `[]` and
-- `⟨⟩` clauses, which turns all three cases into `Tgt`-level transport puzzles,
-- whereas `grade-++ᶜˡ`/`∈-++ᶜˡ` are subst-free by construction. That means
-- restating `wk-ren-⟨ρ⟩-ctx-tgt` over `∈-++ᶜˡ` too, and so moving
-- `grade-++ᶜˡ`/`∈-++ᶜˡ` down into `RenEquivalence` beside the other
-- variable-relocation lemmas.

-- SUBSTITUTION FIXES A RESOURCE VARIABLE
--
-- The `rvar` counterparts of `sub-var-r`/`sub-var-l`: `⟨_⟩[_↦_]rvar` returns the
-- same cell when the variable it replaces is a different one. Simpler than the
-- value versions — a box type is never eternal, so there is no `eternal?` split.

sub-rvar-r : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
           → (z : [ ρ ] A ∈[ σ ] Θ)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → Tgt-cast (castOf {Γ} {B} Θ)
               (rvar-tgt (∈-++ᶜʳ {Γ = Γ ∷ B} z)
                         (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
           ≡ (σ , ∈-++ᶜʳ {Γ = Γ} z)

sub-rvar-r {Γ} {B} (Θ ∷ C) Hd W = Tgt-cast-Hd (castOf {Γ} {B} (Θ ∷ C))

sub-rvar-r {Γ} {B} (Θ ∷ C) (Tl-∷ z) W =
  trans (Tgt-cast-irr (castOf {Γ} {B} (Θ ∷ C))
                      (cong (_∷ C) (castOf {Γ} {B} Θ)) _)
    (trans (Tgt-cast-∷ (castOf {Γ} {B} Θ) _)
           (cong Tgt-∷ (sub-rvar-r Θ z W)))

sub-rvar-r {Γ} {B} (Θ ⟨ ρ' ⟩) (Tl-⟨⟩ z) W =
  trans (Tgt-cast-irr (castOf {Γ} {B} (Θ ⟨ ρ' ⟩))
                      (cong (_⟨ ρ' ⟩) (castOf {Γ} {B} Θ)) _)
    (trans (Tgt-cast-⟨⟩ ρ' (castOf {Γ} {B} Θ) _)
           (cong (Tgt-⟨⟩ ρ') (sub-rvar-r Θ z W)))

sub-rvar-l : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
           → (z : [ ρ ] A ∈[ σ ] Γ)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → Tgt-cast (castOf {Γ} {B} Θ)
               (rvar-tgt (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z))
                         (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
           ≡ (grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ} Θ z)

sub-rvar-l {Γ} {B} [] z W = refl

sub-rvar-l {Γ} {B} (Θ ∷ C) z W =
  trans (Tgt-cast-irr (castOf {Γ} {B} (Θ ∷ C))
                      (cong (_∷ C) (castOf {Γ} {B} Θ)) _)
    (trans (Tgt-cast-∷ (castOf {Γ} {B} Θ) _)
           (cong Tgt-∷ (sub-rvar-l Θ z W)))

sub-rvar-l {Γ} {B} (Θ ⟨ ρ' ⟩) z W =
  trans (Tgt-cast-irr (castOf {Γ} {B} (Θ ⟨ ρ' ⟩))
                      (cong (_⟨ ρ' ⟩) (castOf {Γ} {B} Θ)) _)
    (trans (Tgt-cast-⟨⟩ ρ' (castOf {Γ} {B} Θ) _)
           (cong (Tgt-⟨⟩ ρ') (sub-rvar-l Θ z W)))

-- The same, taking the cell's location as an equation rather than reading it off
-- with `proj₂` — which is dependent, so `cong proj₂` is not available.

sub-rvar-r′ : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ} → (z : [ ρ ] A ∈[ σ ] Θ)
            → (t : Tgt ((Γ ∷ B) ++ᶜ Θ) ([ ρ ] A))
            → t ≡ (σ , ∈-++ᶜʳ {Γ = Γ ∷ B} z)
            → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
            → Tgt-cast (castOf {Γ} {B} Θ)
                (rvar-tgt (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
            ≡ (σ , ∈-++ᶜʳ {Γ = Γ} z)
sub-rvar-r′ Θ z t refl W = sub-rvar-r Θ z W

sub-rvar-l′ : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ} → (z : [ ρ ] A ∈[ σ ] Γ)
            → (t : Tgt ((Γ ∷ B) ++ᶜ Θ) ([ ρ ] A))
            → t ≡ (grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z))
            → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
            → Tgt-cast (castOf {Γ} {B} Θ)
                (rvar-tgt (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
            ≡ (grade-++ᶜˡ σ Θ , ∈-++ᶜˡ {Γ = Γ} Θ z)
sub-rvar-l′ Θ z t refl W = sub-rvar-l Θ z W

-- The cell a weakened-then-substituted `unbox` names is the original one: the
-- renaming pushes it (`cong-ren-tgt-r`/`-l`, by which side `∈-++ᶜ-split` says it
-- came from) and the substitution puts it back (`sub-rvar-r`/`-l`).

unbox-cell-wk : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ σ}
              → (c : [ ρ ] A ∈[ σ ] (Γ ++ᶜ Θ))
              → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
              → Tgt-cast (castOf {Γ} {B} Θ)
                  (rvar-tgt
                     (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (wk-ren {A = B})) c))
                     (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
              ≡ (σ , c)

unbox-cell-wk {Γ} {B} Θ c W with ∈-++ᶜ-split Γ Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ Γ Θ c c' eqc =
  sub-rvar-r′ Θ c' _ (cong-ren-tgt-r (wk-ren {A = B}) c') W

... | inj₁ (σ' , c') =
  subst (λ t → Tgt-cast (castOf {Γ} {B} Θ)
                 (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                                           (proj₂ t)))
                           (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W)
             ≡ t)
        (sym (∈-++ᶜ-split-inj₁ Γ Θ c c' eqc))
        (sub-rvar-l′ Θ c' _ (cong-ren-tgt-l (wk-ren {A = B}) Θ c') W)

-- SUBSTITUTING FOR A FRESHLY WEAKENED VARIABLE: THE VARIABLE CASE
--
-- The weakening's image never *is* the substituted variable, so a variable comes
-- back unchanged. Which of `sub-var-r`/`sub-var-l` applies depends on whether it
-- came from the suffix or the prefix, and `∈-++ᶜ-split` decides that.

sub-wk-var-r : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ} → (z : A ∈[ ρ ] Θ)
             → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
             → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                            (var f (∈-++ᶜʳ {Γ = Γ} z)))
                    [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
             ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ} z)

sub-wk-var-r {Γ} {B} Θ z W f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {Γ} {B} Θ)
      (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) (≐ᵛ-refl W)
        (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                       (∈-++ᶜʳ {Γ = Γ} z) f
                       (cong-ren-tgt-r (wk-ren {A = B}) z) f)))
    (sub-var-r Θ z W f f')

sub-wk-var-l : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ} → (z : A ∈[ ρ ] Γ)
             → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
             → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                            (var f (∈-++ᶜˡ {Γ = Γ} Θ z)))
                    [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
             ≐ᵛ var f' (∈-++ᶜˡ {Γ = Γ} Θ z)

sub-wk-var-l {Γ} {B} Θ z W f f' =
  ≐ᵛ-trans
    (castᵛ-≐ (castOf {Γ} {B} Θ)
      (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) (≐ᵛ-refl W)
        (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                       (∈-++ᶜˡ {Γ = Γ} Θ z) f
                       (cong-ren-tgt-l (wk-ren {A = B}) Θ z) f)))
    (sub-var-l Θ z W f f')

sub-wk-var : ∀ {Γ B} → (Θ : Ctx) → ∀ {A ρ} → (y : A ∈[ ρ ] (Γ ++ᶜ Θ))
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → castᵛ (castOf {Γ} {B} Θ)
               ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) (var f y))
                  [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
           ≐ᵛ var f' y

sub-wk-var {Γ} {B} Θ {A} {ρ} y W f f' with ∈-++ᶜ-split Γ Θ y in eq

... | inj₂ z
  rewrite ∈-++ᶜ-split-inj₂ Γ Θ y z eq = sub-wk-var-r Θ z W f f'

... | inj₁ (ρ' , z) =
  subst (λ t → (fu f'u : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
             → castᵛ (castOf {Γ} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                            (var fu (proj₂ t)))
                    [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
             ≐ᵛ var f'u (proj₂ t))
        (sym (∈-++ᶜ-split-inj₁ Γ Θ y z eq))
        (λ fu f'u → sub-wk-var-l Θ z W fu f'u)
        f f'

-- SUBSTITUTING FOR A FRESHLY WEAKENED VARIABLE
--
-- Mutual induction on the term, at an arbitrary suffix: each binding former
-- grows it, which costs nothing — `cong-ren {Θ ∷ A} r` *is*
-- `cong-∷-ren (cong-ren {Θ} r)` and `split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ ∷ A})` *is*
-- `Tl-∷ (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))`, both definitionally, and
-- `split-l` is unchanged so the substituted value keeps its type. What is left
-- per case is pushing the cast through the former and reconciling the two
-- (equal) context proofs by `castᶜ-irr` — whose two arguments must be given
-- explicitly, since nothing determines them.

mutual

  sub-wk-V : ∀ {Γ B} → (Θ : Ctx) → ∀ {A} → (U : (Γ ++ᶜ Θ) ⊢V⦂ A)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → castᵛ (castOf {Γ} {B} Θ)
               ((V-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) U)
                  [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]v)
           ≐ᵛ U

  sub-wk-V {Γ} {B} Θ (var f y) W = sub-wk-var Θ y W f f
  sub-wk-V {Γ} {B} Θ (const c) W = ≡→≐ᵛ (cast-const (castOf {Γ} {B} Θ))
  sub-wk-V {Γ} {B} Θ ⋆         W = ≡→≐ᵛ (cast-⋆ (castOf {Γ} {B} Θ))
  sub-wk-V {Γ} {B} Θ ⦉ V₁ , V₂ ⦊ W =
    ≐ᵛ-trans (≡→≐ᵛ (cast-pair (castOf {Γ} {B} Θ)))
             (pair-≐ (sub-wk-V Θ V₁ W) (sub-wk-V Θ V₂ W))
  sub-wk-V {Γ} {B} Θ {A = A ⇒ C} (lam M) W =
    ≐ᵛ-trans (≡→≐ᵛ (cast-lam (castOf {Γ} {B} Θ) _))
             (lam-≐ (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                               (castOf {Γ} {B} (Θ ∷ A)) _))
                              (sub-wk-C (Θ ∷ A) M W)))

  sub-wk-C : ∀ {Γ B} → (Θ : Ctx) → ∀ {C} → (M : (Γ ++ᶜ Θ) ⊢C⦂ C)
           → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
           → castᶜ (castOf {Γ} {B} Θ)
               ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B})) M)
                  [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
           ≐ᶜ M

  sub-wk-C {Γ} {B} Θ (return V) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-ret (castOf {Γ} {B} Θ))) (return-≐ (sub-wk-V Θ V W))

  sub-wk-C {Γ} {B} Θ (_⨟_ {A = A} {ε = ε} M N) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-seq (castOf {Γ} {B} Θ)))
      (seq-≐ (sub-wk-C Θ M W)
             (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr
                                (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ} {B} Θ))
                                (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))
                       (sub-wk-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)))

  sub-wk-C {Γ} {B} Θ (V₁ · V₂) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-app (castOf {Γ} {B} Θ)))
             (app-≐ (sub-wk-V Θ V₁ W) (sub-wk-V Θ V₂ W))

  sub-wk-C {Γ} {B} Θ (match_`in_ {A = A} {B = B'} V N) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-match (castOf {Γ} {B} Θ)))
      (match-≐ (sub-wk-V Θ V W)
               (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr
                                  (cong (λ Γ₀ → Γ₀ ∷ A ∷ B') (castOf {Γ} {B} Θ))
                                  (castOf {Γ} {B} (Θ ∷ A ∷ B')) _))
                         (sub-wk-C (Θ ∷ A ∷ B') N W)))

  sub-wk-C {Γ} {B} Θ (absurd V) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-absurd (castOf {Γ} {B} Θ)))
             (absurd-≐ (sub-wk-V Θ V W))

  sub-wk-C {Γ} {B} Θ (perform op V M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-perform (castOf {Γ} {B} Θ)))
      (perform-≐ (sub-wk-V Θ V W)
                 (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr
                                    (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                    ∷ type-of-gtype (arity op))
                                          (castOf {Γ} {B} Θ))
                                    (castOf {Γ} {B}
                                      (Θ ⟨ mapᵉ (op-grade op) ⟩
                                         ∷ type-of-gtype (arity op))) _))
                           (sub-wk-C (Θ ⟨ mapᵉ (op-grade op) ⟩
                                        ∷ type-of-gtype (arity op)) M W)))

  sub-wk-C {Γ} {B} Θ (delay τ M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-delay (castOf {Γ} {B} Θ)))
      (delay-≐ (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr
                                  (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ} {B} Θ))
                                  (castOf {Γ} {B} (Θ ⟨ of-natʳ τ ⟩)) _))
                         (sub-wk-C (Θ ⟨ of-natʳ τ ⟩) M W)))

  sub-wk-C {Γ} {B} Θ (box {A = A} {ρ = ρ} V M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-box (castOf {Γ} {B} Θ)))
      (box-≐ (≐ᵛ-trans (≡→≐ᵛ (castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ ρ ⟩)) _))
                       (sub-wk-V (Θ ⟨ ρ ⟩) V W))
             (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ [ ρ ] A)) _))
                       (sub-wk-C (Θ ∷ [ ρ ] A) M W)))

  sub-wk-C {Γ} {B} Θ (coerce p M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cast-coerce (castOf {Γ} {B} Θ)))
             (coerce-≐ (sub-wk-C Θ M W))

  -- `handle`: dispatch on whether the weakened type is eternal. Matching a `Dec`
  -- *argument* rather than `with eternal? B` is what keeps this typeable — a
  -- `with` would abstract `eternal? B` in the goal, and the two halves' own
  -- statements (which re-elaborate it) would then no longer match.
  sub-wk-C {Γ} {B} Θ (handle M `with H `in N) W = go (eternal? B)
    where
      go : Dec (Eternal B) → _
      go (yes et) = sub-wk-handle-et Θ et M H N W
      go (no ¬et) = sub-wk-handle-ne Θ ¬et M H N W

  sub-wk-C {Γ} {B} Θ (unbox {A = A} {ρ = ρ} w V M) W =
    ≐ᶜ-trans
      (castᶜ-≐ (castOf {Γ} {B} Θ)
        (sub-unbox (rn ∘ʳ w) V
                   (C-rename (cong-ren {Γ'' = Θ ∷ A} (wk-ren {A = B})) M)
                   z₀ W relv))
      (≐ᶜ-trans (≡→≐ᶜ (cast-unbox (castOf {Γ} {B} Θ)))
        (unbox-≐ cell
          (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                     (castOf {Γ} {B} (Θ ∷ A)) _))
                    (sub-wk-C (Θ ∷ A) M W))))
    where
      rn = cong-ren {Γ'' = Θ} (wk-ren {A = B})
      z₀ = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})

      v = proj₂ (rvar-tgt (proj₂ (unbox-tgt (rn ∘ʳ w) V)) z₀ W)

      -- the bound the substitution itself builds
      relv = ≾ᵣ-trans (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt (rn ∘ʳ w) V) ⟩[ z₀ ↦ W ]rvar)))
                      (proj₂ (proj₂ (unbox⇒var (rn ∘ʳ w) V)))

      cell : unbox-tgt (castʳᵉ (castOf {Γ} {B} Θ) (unbox-var-ren v relv))
                       (var {A = [ ρ ] A} (λ _ → ≾ᵣ-refl) Hd)
           ≡ unbox-tgt w V
      cell =
        trans (unbox-tgt-castʳᵉ (castOf {Γ} {B} Θ) (unbox-var-ren v relv)
                                (var {A = [ ρ ] A} (λ _ → ≾ᵣ-refl) Hd))
          (trans (cong (Tgt-cast (castOf {Γ} {B} Θ)) (unbox-var-tgt v relv))
            (trans (cong (λ t → Tgt-cast (castOf {Γ} {B} Θ)
                                  (rvar-tgt (proj₂ t)
                                     (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) W))
                         (unbox-tgt-∘ rn w V))
                   (unbox-cell-wk Θ (proj₂ (unbox-tgt w V)) W)))

  -- `sub-wk-C` with its context given by an equation rather than literally, so
  -- that the eternal `handle` clause below can recurse on the bare subterm:
  -- casting the argument into shape is not structurally smaller, and the
  -- termination checker rejects it.

  sub-wk-C-cast : ∀ {Γ B Γ₀} → (Θ : Ctx) → (e : Γ₀ ≡ Γ ++ᶜ Θ) → ∀ {C}
                → (M : Γ₀ ⊢C⦂ C)
                → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
                → castᶜ (castOf {Γ} {B} Θ)
                    ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                               (subst (_⊢C⦂ C) e M))
                       [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
                ≐ᶜ subst (_⊢C⦂ C) e M

  sub-wk-C-cast Θ refl M W = sub-wk-C Θ M W

  -- `handle`, eternal. `restrict-ren wk-ren` is `wk-ren` there, so the clause is
  -- weakened by the eternal `B` and then substituted at it — another instance of
  -- `sub-wk-C`, at the *splitting's own halves* `split-l z₀ ᴱ` and
  -- `split-r z₀ ᴱ ++ᶜ D`. Taking them rather than `Γ ᴱ`, `Θ ᴱ ++ᶜ D` is what
  -- makes the two ways of naming the substituted variable the *same splitting*,
  -- so `split→∈-unique` settles it outright; the resulting mismatch with the
  -- renaming (which `restrict-wk-clause-≐` delivers at `Γ ᴱ`, `Θ ᴱ`) is a
  -- relocation of two contexts, which `cong-ren-wk-cast-≐` discharges by
  -- matching both equalities. The transports left over form a loop.

  sub-wk-handle-et : ∀ {Γ B} → (Θ : Ctx) → ∀ {A B' ε ε'}
                   → (et : Eternal B)
                   → (M : (Γ ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                   → (H : (op : Op) → (ε'' : E) →
                            (Γ ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                            ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                   → (N : (Γ ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                   → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
                   → castᶜ (castOf {Γ} {B} Θ)
                       ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                                  (handle M `with H `in N))
                          [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
                   ≐ᶜ (handle M `with H `in N)

  sub-wk-handle-et {Γ} {B} Θ {A = A} {B' = B'} {ε = ε} et M H N W
    rewrite eternal?-yes et =
    ≐ᶜ-trans (≡→≐ᶜ (cast-handle (castOf {Γ} {B} Θ)))
      (handle-≐ (sub-wk-C Θ M W)
        (λ op ε'' → clause op ε'')
        (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr
                           (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ} {B} Θ))
                           (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))
                  (sub-wk-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)))
    where
      z₀ = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})

      e₁ : (Γ ++ᶜ Θ) ᴱ ≡ Γ ᴱ ++ᶜ Θ ᴱ
      e₁ = ᴱ-++ᶜ Γ Θ

      e₂ : ((Γ ∷ B) ++ᶜ Θ) ᴱ ≡ (Γ ᴱ ∷ B) ++ᶜ Θ ᴱ
      e₂ = trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                 (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))

      clause : (op : Op) → (ε'' : E) → _
      clause op ε'' =
        ≐ᶜ-trans (castᶜ-≐ cOut (substᶜ-≐ bigE (sub-≐ᶜ v (≐ᵛ-refl _) ren-step)))
          (≐ᶜ-trans (≡→≐ᶜ (cong (λ t → castᶜ cOut (subst (_⊢C⦂ CT) bigE t))
                                sub-step))
            (≐ᶜ-trans (≡→≐ᶜ reshape)
              (≐ᶜ-trans (substᶜ-≐ resid (sub-wk-C-cast Θ₀ F₁ (H op ε'') W₁))
                        (≡→≐ᶜ (trans (subst-fuseᶜ F₁ resid (H op ε''))
                                     (subst-loopᶜ _ (H op ε'')))))))
        where
          D = [] ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B' ‼ ε'')

          CT = B' ‼ (op-grade op ·ₑ ε'')

          s = split-++ʳ (∈-ᴱ-split et z₀) D

          -- the transport the substitution's own eternal clause applies
          bigE : split-l (split→∈ s) ++ᶜ split-r (split→∈ s)
               ≡ (split-l z₀ ++ᶜ split-r z₀) ᴱ ++ᶜ D
          bigE = trans (cong₂ _++ᶜ_ (split→∈-split-l s) (split→∈-split-r s))
                   (trans (sym (++ᶜ-assoc ((split-l z₀) ᴱ) ((split-r z₀) ᴱ) D))
                          (cong (_++ᶜ D) (sym (ᴱ-++ᶜ (split-l z₀) (split-r z₀)))))

          cOut : (split-l z₀ ++ᶜ split-r z₀) ᴱ ++ᶜ D ≡ (Γ ++ᶜ Θ) ᴱ ++ᶜ D
          cOut = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ)

          -- the renaming, fused: at this suffix the associativity legs are `refl`
          rfuse : cong-ren {Γ'' = D} (restrict-ren {Ξ = []}
                                       (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                ≐ʳ (eq-ren (cong (_++ᶜ D) (sym e₂))
                    ∘ʳ cong-ren {Γ'' = Θ ᴱ ++ᶜ D} (wk-ren {A = B})
                    ∘ʳ eq-ren (cong (_++ᶜ D) e₁))
          rfuse =
            ≐ʳ-trans (restrict-wk-clause-≐ et Θ D e₁ e₂)
                     (∘ʳ-≐ ≐ʳ-refl
                           (∘ʳ-≐ (≐ʳ-trans (∘ʳ-identityˡ-≐ _)
                                           (∘ʳ-identityʳ-≐ _))
                                 ≐ʳ-refl))

          -- the recursion's context: the splitting's own halves
          Γ₀ = split-l z₀ ᴱ
          Θ₀ = split-r z₀ ᴱ ++ᶜ D

          eLΓ : split-l z₀ ᴱ ≡ Γ ᴱ
          eLΓ = cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))

          eRΘ : split-r z₀ ᴱ ++ᶜ D ≡ Θ ᴱ ++ᶜ D
          eRΘ = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D)
                     (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B} {Θ}))

          eIn : Γ ᴱ ++ᶜ (Θ ᴱ ++ᶜ D) ≡ Γ₀ ++ᶜ Θ₀
          eIn = sym (cong₂ _++ᶜ_ eLΓ eRΘ)

          eOut′ : (Γ₀ ∷ B) ++ᶜ Θ₀ ≡ (Γ ᴱ ∷ B) ++ᶜ (Θ ᴱ ++ᶜ D)
          eOut′ = cong₂ (λ Γ₁ Θ₁ → (Γ₁ ∷ B) ++ᶜ Θ₁) eLΓ eRΘ

          F₁ : (Γ ++ᶜ Θ) ᴱ ++ᶜ D ≡ Γ₀ ++ᶜ Θ₀
          F₁ = trans (cong (_++ᶜ D) e₁) eIn

          F₂ : (Γ₀ ∷ B) ++ᶜ Θ₀ ≡ ((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ D
          F₂ = trans eOut′ (cong (_++ᶜ D) (sym e₂))

          wk₀ = cong-ren {Γ'' = Θ₀} (wk-ren {A = B})

          -- the two names for the substituted variable are the same splitting
          x₁ = split→∈ (split-≡-++ᶜ {Γ₀ ∷ B} {Θ₀})
          v  = split→∈ s

          var-eq : subst (λ Γ₁ → B ∈[ ctx-grade Θ₀ ] Γ₁) F₂ x₁ ≡ v
          var-eq = split→∈-unique F₂ (split-≡-++ᶜ {Γ₀ ∷ B} {Θ₀}) s

          Wᴱ : split-l v ⊢V⦂ B
          Wᴱ = subst (_⊢V⦂ B) (sym (split→∈-split-l s))
                     (eternal-val-restrict et W)

          eW : split-l x₁ ≡ split-l v
          eW = trans (split-l-cast F₂ x₁) (cong split-l var-eq)

          W₁ : split-l x₁ ⊢V⦂ B
          W₁ = subst (_⊢V⦂ B) (sym eW) Wᴱ

          Y = C-rename wk₀ (subst (_⊢C⦂ CT) F₁ (H op ε''))

          rfuse2 : cong-ren {Γ'' = D} (restrict-ren {Ξ = []}
                              (cong-ren {Γ'' = Θ} (wk-ren {A = B})))
                 ≐ʳ (eq-ren (cong (_++ᶜ D) (sym e₂))
                     ∘ʳ (eq-ren eOut′ ∘ʳ wk₀ ∘ʳ eq-ren eIn)
                     ∘ʳ eq-ren (cong (_++ᶜ D) e₁))
          rfuse2 =
            ≐ʳ-trans rfuse
              (∘ʳ-≐ ≐ʳ-refl
                (∘ʳ-≐ (cong-ren-wk-cast-≐ Γ₀ (Γ ᴱ) Θ₀ (Θ ᴱ ++ᶜ D)
                                          eLΓ eRΘ eIn eOut′)
                      ≐ʳ-refl))

          -- the renaming, split into its legs, each `eq-ren` becoming its
          -- transport
          ren-step : C-rename (cong-ren {Γ'' = D} (restrict-ren {Ξ = []}
                                  (cong-ren {Γ'' = Θ} (wk-ren {A = B}))))
                              (H op ε'')
                   ≐ᶜ subst (_⊢C⦂ CT) F₂ Y
          ren-step =
            ≐ᶜ-trans (C-rename-≐ rfuse2 (H op ε''))
              (≐ᶜ-trans (C-rename-∘ _ _ (H op ε''))
                (≐ᶜ-trans (C-rename-eq-≐ (cong (_++ᶜ D) (sym e₂)) ≐ʳ-refl _)
                  (≐ᶜ-trans
                    (substᶜ-≐ (cong (_++ᶜ D) (sym e₂))
                      (≐ᶜ-trans (C-rename-∘ _ (eq-ren (cong (_++ᶜ D) e₁))
                                            (H op ε''))
                        (≐ᶜ-trans (C-rename-cong _
                                    (C-rename-eq-≐ (cong (_++ᶜ D) e₁) ≐ʳ-refl _))
                          (≐ᶜ-trans (C-rename-∘ (eq-ren eOut′) _ _)
                            (≐ᶜ-trans (C-rename-eq-≐ eOut′ ≐ʳ-refl _)
                              (substᶜ-≐ eOut′
                                (≐ᶜ-trans (C-rename-∘ wk₀ (eq-ren eIn) _)
                                          (C-rename-cong wk₀
                                            (C-rename-eq-≐ eIn ≐ʳ-refl _)))))))))
                    (≡→≐ᶜ (trans (subst-fuseᶜ eOut′ (cong (_++ᶜ D) (sym e₂)) _)
                                 (cong (λ t → subst (_⊢C⦂ CT) F₂ (C-rename wk₀ t))
                                       (subst-fuseᶜ (cong (_++ᶜ D) e₁) eIn
                                                    (H op ε''))))))))

          -- the substitution, moved across the outer transport
          sub-step : (subst (_⊢C⦂ CT) F₂ Y) [ v ↦ Wᴱ ]c
                   ≡ subst (_⊢C⦂ CT)
                       (cong₂ _++ᶜ_ eW
                              (trans (split-r-cast F₂ x₁) (cong split-r var-eq)))
                       (Y [ x₁ ↦ W₁ ]c)
          sub-step =
            sub-cast-C′ F₂ Y x₁ v var-eq W₁ Wᴱ (subst-subst-sym′ eW Wᴱ)

          resid : Γ₀ ++ᶜ Θ₀ ≡ (Γ ++ᶜ Θ) ᴱ ++ᶜ D
          resid = sym F₁

          Z = Y [ x₁ ↦ W₁ ]c

          G : split-l x₁ ++ᶜ split-r x₁ ≡ split-l v ++ᶜ split-r v
          G = cong₂ _++ᶜ_ eW (trans (split-r-cast F₂ x₁) (cong split-r var-eq))

          -- the goal's three transports and the recursion's own one both take
          -- `Z` to the clause's context, so they agree by `uip`
          reshape : castᶜ cOut (subst (_⊢C⦂ CT) bigE (subst (_⊢C⦂ CT) G Z))
                  ≡ subst (_⊢C⦂ CT) resid (castᶜ (castOf {Γ₀} {B} Θ₀) Z)
          reshape =
            trans (castᶜ≡subst cOut _)
              (trans (cong (subst (_⊢C⦂ CT) cOut) (subst-fuseᶜ G bigE Z))
                (trans (subst-fuseᶜ (trans G bigE) cOut Z)
                  (sym (trans (cong (subst (_⊢C⦂ CT) resid)
                                    (castᶜ≡subst (castOf {Γ₀} {B} Θ₀) Z))
                         (trans (subst-fuseᶜ (castOf {Γ₀} {B} Θ₀) resid Z)
                                (cong (λ z → subst (_⊢C⦂ CT) z Z)
                                      (uip {p = trans (castOf {Γ₀} {B} Θ₀) resid}
                                           {q = trans (trans G bigE) cOut})))))))

  -- `handle`, non-eternal. The clause's renaming `restrict-ren (cong-ren {Θ}
  -- wk-ren)` is identity-like (`restrict-wk-≐`), so the clause is transported
  -- three times — by it, by the substitution's `ᴱ-drop-split`, and by the outer
  -- cast — around a loop, which `subst-loop₃` collapses.
  --
  -- Stated over the unreduced substitution and doing its own `with`, so that the
  -- `yes` case is dismissed by absurdity rather than appearing in any statement.

  sub-wk-handle-ne : ∀ {Γ B} → (Θ : Ctx) → ∀ {A B' ε ε'}
                   → ¬ Eternal B
                   → (M : (Γ ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                   → (H : (op : Op) → (ε'' : E) →
                            (Γ ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                              ∷ [ mapᵉ (op-grade op) ]
                                  (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                            ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                   → (N : (Γ ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                   → (W : split-l (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})) ⊢V⦂ B)
                   → castᶜ (castOf {Γ} {B} Θ)
                       ((C-rename (cong-ren {Γ'' = Θ} (wk-ren {A = B}))
                                  (handle M `with H `in N))
                          [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) ↦ W ]c)
                   ≐ᶜ (handle M `with H `in N)

  sub-wk-handle-ne {Γ} {B} Θ {A = A} {B' = B'} {ε = ε} ¬et M H N W
    rewrite eternal?-no ¬et =
    ≐ᶜ-trans (≡→≐ᶜ (cast-handle (castOf {Γ} {B} Θ)))
      (handle-≐ (sub-wk-C Θ M W)
        (λ op ε'' → clause op ε'')
        (≐ᶜ-trans (≡→≐ᶜ (castᶜ-irr
                           (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ} {B} Θ))
                           (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))
                  (sub-wk-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)))
    where
      z₀ = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})

      e₁ : (Γ ++ᶜ Θ) ᴱ ≡ ((Γ ∷ B) ++ᶜ Θ) ᴱ
      e₁ = sym (trans (ᴱ-drop-split ¬et z₀) (cong _ᴱ (castOf {Γ} {B} Θ)))

      clause : (op : Op) → (ε'' : E) → _
      clause op ε'' =
        ≐ᶜ-trans
          (castᶜ-≐ (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ))
            (substᶜ-≐′ (λ Γ₀ → Γ₀ ++ᶜ D)
                       {C = CT} (ᴱ-drop-split ¬et z₀)
              (C-rename-eq-≐ (cong (_++ᶜ D) e₁)
                (≐ʳ-trans (cong-ren-≐ D (restrict-wk-≐ ¬et Θ e₁))
                          (cong-ren-eq-ren-≐ D e₁))
                (H op ε''))))
          (≡→≐ᶜ collapse)
        where
          D = [] ∷ type-of-gtype (param op)
                 ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ B' ‼ ε'')

          CT = B' ‼ (op-grade op ·ₑ ε'')

          collapse : castᶜ (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ))
                       (subst (λ Γ₀ → (Γ₀ ++ᶜ D) ⊢C⦂ CT) (ᴱ-drop-split ¬et z₀)
                         (subst (_⊢C⦂ CT) (cong (_++ᶜ D) e₁) (H op ε'')))
                   ≡ H op ε''
          collapse =
            trans (castᶜ≡subst (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ)) _)
              (trans (cong (subst (_⊢C⦂ CT)
                              (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ)))
                           (subst-++ᶜʳ D (ᴱ-drop-split ¬et z₀) _))
                     (subst-loop₃ (cong (_++ᶜ D) e₁)
                                  (cong (_++ᶜ D) (ᴱ-drop-split ¬et z₀))
                                  (cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D) (castOf {Γ} {B} Θ))
                                  (H op ε'')))



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

env-Vˢ-var-r (renᵉ γ r) Δ x f f' =
  ≐ᵛ-trans (env-Vˢ-≐ γ Δ (ren-var-r r x f f)) (env-Vˢ-var-r γ Δ x f f')

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

env-Vˢ-var-l (renᵉ γ r) Δ eγ ¬et p x f f' =
  ≐ᵛ-trans
    (env-Vˢ-≐ γ Δ
      (var-ren-tgt-≐ (cong-ren {Γ'' = Δ} r) (∈-++ᶜˡ Δ x) f
                     (cong-ren-tgt-l r Δ x) f₂))
    (≐ᵛ-trans (env-Vˢ-var-l γ Δ eγ ¬et p (proj₂ (var-tgt r x)) f₂ f₃)
              (V-rename-cong (push-ren Δ p)
                (env-Vˢ-≐ γ [] (≐ᵛ-sym (var-ren-≐ r x f' f₃)))))
  where
    drop = proj₁ (proj₂ (var-rename r x))
    f₂   = λ z → ≾ᵣ-trans (grade-++ᶜˡ-mono Δ (drop z)) (f z)
    f₃   = λ z → ≾ᵣ-trans (drop z) (f' z)

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

env-var ⌊ St ⌋       pγ x f = pγ x f

env-var (∅ᵉ St)       pγ x f = ⊥-elim (not-in-empty-ctx x)

env-var (sliceᵉ γ q) pγ x f = Val-slice q _ (env-var γ pγ x f)

env-var (renᵉ γ r)   pγ x f =
  Val-≐ᵛ _ (≐ᵛ-sym (env-Vˢ-≐ γ [] (var-ren-≐ r x f f')))
           (env-var γ pγ (proj₂ (var-tgt r x)) f')
  where
    f' = λ ¬et → ≾ᵣ-trans (proj₁ (proj₂ (var-rename r x)) ¬et) (f ¬et)

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
