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
-- RENAMING COMMUTES WITH SUBSTITUTION
--
-- Renaming a prefix and substituting at the variable just past it are
-- independent, so they may be done in either order — the value substituted
-- picking up the renaming when it goes second. Stated at an arbitrary suffix,
-- as `sub-wk`, and for the same reason: every binding former grows it.
------------------------------------------------------------------------

-- The three renamings the variable substitution puts in front of its recursive
-- call are natural in a renaming of the prefix.

wk-ren-nat : ∀ {Γ Γ' A} → (r : Ren [] Γ Γ')
           → (cong-∷-ren {A = A} r ∘ʳ wk-ren) ≐ʳ (wk-ren ∘ʳ r)
wk-ren-nat r = mk≐ʳ (λ y → cong-ren-tgt-l r ([] ∷ _) y)

⟨⟩-ren-nat : ∀ {Γ Γ' ρ} → (r : Ren [] Γ Γ')
           → (rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩))
           → (∀ {A σ} → (y : A ∈[ σ ] Γ') → var-tgt rn y ≡ Tgt-⟨⟩ ρ (σ , y))
           → (∀ {A σ} → (y : A ∈[ σ ] Γ)  → var-tgt rn y ≡ Tgt-⟨⟩ ρ (σ , y))
           → (cong-⟨⟩-ren r ∘ʳ rn) ≐ʳ (rn ∘ʳ r)
⟨⟩-ren-nat {ρ = ρ} r rn h' h = mk≐ʳ go
  where
    go : ∀ {A σ} → (y : A ∈[ σ ] _) → _
    go y =
      trans (cong (var-tgt′ (cong-⟨⟩-ren r)) (h y))
            (sym (h' (proj₂ (var-tgt r y))))

hit-⟨⟩-tgt : ∀ {Γ A σ ρ} → (p : ρ ≾ᵣ uᵣ) → (y : A ∈[ σ ] Γ)
           → var-tgt (⟨⟩-≤-ren p ∘ʳ ⟨⟩-η⁻¹-ren {Δ = Γ}) y ≡ Tgt-⟨⟩ ρ (σ , y)
hit-⟨⟩-tgt p y = cong (var-tgt′ (⟨⟩-≤-ren p)) (⟨⟩-η⁻¹-tgt y)

-- An eternal extension is natural: it builds only variables, constants, `⋆` and
-- pairs, so a renaming passes through it.

eternal-val-ext-ren : ∀ {Γ Γ' A ρ} → (et : Eternal A) → (r : Ren [] Γ Γ')
                    → (V : Γ ⊢V⦂ A)
                    → V-rename (cong-⟨⟩-ren {ρ = ρ} r) (eternal-val-ext et V)
                    ≐ᵛ eternal-val-ext et (V-rename r V)
eternal-val-ext-ren et             r (var f x)   = var-≐
eternal-val-ext-ren et             r (const c)   = const-≐
eternal-val-ext-ren et             r ⋆           = ⋆-≐
eternal-val-ext-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊ =
  pair-≐ (eternal-val-ext-ren et₁ r V₁) (eternal-val-ext-ren et₂ r V₂)

-- THE VARIABLE SUBSTITUTED FOR
--
-- Looking up the variable being replaced returns the value, pushed under the
-- suffix — a push the recursion of `⟨_,_⟩[_↦_]var` builds one layer at a time,
-- and each layer is natural in a renaming of the prefix.

ren-sub-hit : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
            → (f f' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (⟨ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}) , f
                   ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W
                    ]var))
            ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                 (⟨ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}) , f'
                  ⟩[ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                     ↦ castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                             (V-rename r W)
                   ]var)

ren-sub-hit r [] W f f' = ≐ᵛ-refl _

ren-sub-hit {Γ} {Γ'} {B} r (Θ ∷ C) W f f' =
  ≐ᵛ-trans
    (≡→≐ᵛ (cong (V-rename (cong-∷-ren (cong-ren {Γ'' = Θ} r)))
                (cast-wk-any (castOf {Γ} {B} (Θ ∷ C)) (castOf {Γ} {B} Θ) _)))
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ (cong-∷-ren (cong-ren {Γ'' = Θ} r)) wk-ren _))
      (≐ᵛ-trans (V-rename-≐ (wk-ren-nat (cong-ren {Γ'' = Θ} r)) _)
        (≐ᵛ-trans (V-rename-∘ wk-ren (cong-ren {Γ'' = Θ} r) _)
          (≐ᵛ-trans (V-rename-cong wk-ren (ren-sub-hit r Θ W f f'))
                    (≡→≐ᵛ (sym (cast-wk-any (castOf {Γ'} {B} (Θ ∷ C))
                                            (castOf {Γ'} {B} Θ) _)))))))

ren-sub-hit {Γ} {Γ'} {B} r (Θ ⟨ ρ ⟩) W f f' with eternal? B

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cong (V-rename (cong-⟨⟩-ren (cong-ren {Γ'' = Θ} r)))
                (cast-ext-any (castOf {Γ} {B} (Θ ⟨ ρ ⟩))
                              (castOf {Γ} {B} Θ) et _)))
    (≐ᵛ-trans (eternal-val-ext-ren et (cong-ren {Γ'' = Θ} r) _)
      (≐ᵛ-trans (eternal-val-ext-cong et (ren-sub-hit r Θ W _ _))
                (≡→≐ᵛ (sym (cast-ext-any (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                         (castOf {Γ'} {B} Θ) et _)))))

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cong (V-rename (cong-⟨⟩-ren ρ₀))
                (cast-ren-⟨⟩-any (castOf {Γ} {B} (Θ ⟨ ρ ⟩))
                                 (castOf {Γ} {B} Θ) rn _)))
    (≐ᵛ-trans (≐ᵛ-sym (V-rename-∘ (cong-⟨⟩-ren ρ₀) rn _))
      (≐ᵛ-trans (V-rename-≐ (⟨⟩-ren-nat ρ₀ rn (λ y → hit-⟨⟩-tgt bd y)
                                              (λ y → hit-⟨⟩-tgt bd y)) _)
        (≐ᵛ-trans (V-rename-∘ rn ρ₀ _)
          (≐ᵛ-trans (V-rename-cong rn (ren-sub-hit r Θ W _ _))
            (≐ᵛ-trans (V-rename-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl) _)
                      (≡→≐ᵛ (sym (cast-ren-⟨⟩-any (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                                  (castOf {Γ'} {B} Θ) rn' _))))))))
  where
    ρ₀ = cong-ren {Γ'' = Θ} r
    bd = ≾ᵣ-zero-productʳ (f ¬et)

    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren bd ∘ʳ ⟨⟩-η⁻¹-ren

    rn' : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn' = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (f' ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

-- The same, taking both variables as equations: what reaches the substitution
-- on either side is `∈-++ᶜˡ Θ Hd`, which is `split→∈` of the splitting only up
-- to `split→∈-∈-++ᶜˡ`.

ren-sub-hit′ : ∀ {Γ Γ' B σ σ'} → (r : Ren [] Γ Γ') → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
             → (y  : B ∈[ σ  ] ((Γ  ∷ B) ++ᶜ Θ))
             → (y' : B ∈[ σ' ] ((Γ' ∷ B) ++ᶜ Θ))
             → (f  : ¬ Eternal B → σ  ≾ᵣ uᵣ)
             → (f' : ¬ Eternal B → σ' ≾ᵣ uᵣ)
             → _≡_ {A = Tgt ((Γ ∷ B) ++ᶜ Θ) B}
                 (σ , y) (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
             → _≡_ {A = Tgt ((Γ' ∷ B) ++ᶜ Θ) B}
                 (σ' , y') (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
             → V-rename (cong-ren {Γ'' = Θ} r)
                 (castᵛ (castOf {Γ} {B} Θ)
                   (⟨ y , f ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                               ↦ castᵛ (sym (split→∈-split-l
                                               (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
             ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                  (⟨ y' , f' ⟩[ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                                ↦ castᵛ (sym (split→∈-split-l
                                                (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                        (V-rename r W) ]var)
ren-sub-hit′ r Θ W _ _ f f' refl refl = ren-sub-hit r Θ W f f'

-- A SUFFIX VARIABLE
--
-- Neither the renaming nor the substitution moves it, in either order.

ren-sub-var-r : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ}
              → (z : A ∈[ ρ ] Θ) → (W : Γ ⊢V⦂ B)
              → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
              → V-rename (cong-ren {Γ'' = Θ} r)
                  (castᵛ (castOf {Γ} {B} Θ)
                    (⟨ ∈-++ᶜʳ {Γ = Γ ∷ B} z , f
                     ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
              ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                   ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                              (var f' (∈-++ᶜʳ {Γ = Γ ∷ B} z)))
                      [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                (V-rename r W) ]v)

ren-sub-var-r {Γ} {Γ'} {B} r Θ z W f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren {Γ'' = Θ} r) (sub-var-r Θ z _ f f))
    (≐ᵛ-trans (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} r) (∈-++ᶜʳ {Γ = Γ} z) f
                             (cong-ren-tgt-r r z) f)
      (≐ᵛ-sym
        (≐ᵛ-trans
          (castᵛ-≐ (castOf {Γ'} {B} Θ)
            (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
              (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (∈-++ᶜʳ {Γ = Γ ∷ B} z) f'
                             (cong-ren-tgt-r (cong-∷-ren r) z) f')))
          (sub-var-r Θ z _ f' f))))

-- A PREFIX VARIABLE
--
-- The substitution fixes it on either side, and the renaming moves it to its
-- own image, pushed under the suffix.

ren-sub-var-l : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ}
              → (z : A ∈[ ρ ] Γ) → (W : Γ ⊢V⦂ B)
              → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ)
              → V-rename (cong-ren {Γ'' = Θ} r)
                  (castᵛ (castOf {Γ} {B} Θ)
                    (⟨ ∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z) , f
                     ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
              ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                   ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                              (var f' (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z))))
                      [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                        ↦ castᵛ (sym (split→∈-split-l
                                        (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                (V-rename r W) ]v)

ren-sub-var-l {Γ} {Γ'} {B} r Θ z W f f' =
  ≐ᵛ-trans (V-rename-cong (cong-ren {Γ'' = Θ} r) (sub-var-l Θ z _ f f))
    (≐ᵛ-trans (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} r) (∈-++ᶜˡ {Γ = Γ} Θ z) f
                             (cong-ren-tgt-l r Θ z) fr)
      (≐ᵛ-sym
        (≐ᵛ-trans
          (castᵛ-≐ (castOf {Γ'} {B} Θ)
            (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
              (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Tl-∷ z)) f'
                             (cong-ren-tgt-l (cong-∷-ren r) Θ (Tl-∷ z)) fr)))
          (sub-var-l Θ (proj₂ (var-tgt r z)) _ fr fr))))
  where
    -- a renaming only lowers a variable's grade, and the suffix's contribution
    -- is monotone in it, so the bound survives
    fr = λ ¬et → ≾ᵣ-trans (grade-++ᶜˡ-mono Θ
                            (proj₁ (proj₂ (var-rename r z)) ¬et))
                          (f ¬et)

-- THE VARIABLE BEING REPLACED
--
-- `ren-sub-hit` with the variable presented as `∈-++ᶜˡ Θ Hd`, which is where
-- the splitting leaves it, and the renamed side folded into the same shape.

ren-sub-var-hd : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → (W : Γ ⊢V⦂ B)
               → (f f' : ¬ Eternal B → grade-++ᶜˡ uᵣ Θ ≾ᵣ uᵣ)
               → V-rename (cong-ren {Γ'' = Θ} r)
                   (castᵛ (castOf {Γ} {B} Θ)
                     (⟨ ∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ}) , f
                      ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                         ↦ castᵛ (sym (split→∈-split-l
                                         (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
               ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                    ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                               (var f' (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ}))))
                       [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                         ↦ castᵛ (sym (split→∈-split-l
                                         (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                 (V-rename r W) ]v)

ren-sub-var-hd {Γ} {Γ'} {B} r Θ W f f' =
  ≐ᵛ-trans
    (ren-sub-hit′ r Θ W (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ}))
                        (∈-++ᶜˡ {Γ = Γ' ∷ B} Θ (Hd {Γ = Γ'})) f f'
                  (sym (split→∈-∈-++ᶜˡ Γ B Θ)) (sym (split→∈-∈-++ᶜˡ Γ' B Θ)))
    (≐ᵛ-sym
      (castᵛ-≐ (castOf {Γ'} {B} Θ)
        (sub-≐ᵛ (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})) (≐ᵛ-refl _)
          (var-ren-tgt-≐ (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                         (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ})) f'
                         (cong-ren-tgt-l (cong-∷-ren r) Θ (Hd {Γ = Γ})) f'))))

-- THE VARIABLE CASE
--
-- Which of the three applies is what `∈-++ᶜ-split` decides, the prefix's own
-- head being the variable replaced.

ren-sub-var : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ}
            → (y : A ∈[ ρ ] ((Γ ∷ B) ++ᶜ Θ)) → (W : Γ ⊢V⦂ B)
            → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (⟨ y , f ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                              ↦ castᵛ (sym (split→∈-split-l
                                              (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
            ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) (var f' y))
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]v)

ren-sub-var {Γ} {Γ'} {B} r Θ {A} {ρ} y W f f'
  with ∈-++ᶜ-split (Γ ∷ B) Θ y in eq

... | inj₂ z
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B) Θ y z eq = ren-sub-var-r r Θ z W f f'

... | inj₁ (ρ'' , z) =
  subst (λ t → (fu f'u : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
             → V-rename (cong-ren {Γ'' = Θ} r)
                 (castᵛ (castOf {Γ} {B} Θ)
                   (⟨ proj₂ t , fu
                    ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
             ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                  ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                             (var f'u (proj₂ t)))
                     [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                               (V-rename r W) ]v))
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B) Θ y z eq))
        (go z)
        f f'
  where
    go : ∀ {ρ₀} → (z₀ : A ∈[ ρ₀ ] (Γ ∷ B))
       → (fu f'u : ¬ Eternal A → grade-++ᶜˡ ρ₀ Θ ≾ᵣ uᵣ)
       → V-rename (cong-ren {Γ'' = Θ} r)
           (castᵛ (castOf {Γ} {B} Θ)
             (⟨ ∈-++ᶜˡ {Γ = Γ ∷ B} Θ z₀ , fu
              ⟩[ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                 ↦ castᵛ (sym (split→∈-split-l
                                 (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]var))
       ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
            ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                       (var f'u (∈-++ᶜˡ {Γ = Γ ∷ B} Θ z₀)))
               [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                 ↦ castᵛ (sym (split→∈-split-l
                                 (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                         (V-rename r W) ]v)
    go Hd        fu f'u = ren-sub-var-hd r Θ W fu f'u
    go (Tl-∷ z₀) fu f'u = ren-sub-var-l r Θ z₀ W fu f'u

-- THE CELL AN `unbox` NAMES, RENAMED AND SUBSTITUTED
--
-- `unbox-cell-wk`'s counterpart: the cell survives both orders. The third case
-- a weakening could not reach is here — the cell may *be* the variable
-- replaced, and then it is the one inside the substituted value, which is of
-- box type and so a variable itself.

rvar-hit-ren : ∀ {Γ Γ' A ρ} → (r : Ren [] Γ Γ') → (Θ : Ctx)
             → (W : Γ ⊢V⦂ [ ρ ] A)
             → var-tgt′ (cong-ren {Γ'' = Θ} r)
                 (Tgt-cast (castOf {Γ} {[ ρ ] A} Θ)
                   (rvar-tgt (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                             (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))) W)))
             ≡ Tgt-cast (castOf {Γ'} {[ ρ ] A} Θ)
                 (rvar-tgt (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                           (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                           (castᵛ (sym (split→∈-split-l
                                          (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ})))
                                  (V-rename r W)))

rvar-hit-ren r [] (var f y) = refl

rvar-hit-ren {Γ} {Γ'} {A} {ρ} r (Θ ∷ C) W =
  trans (cong (var-tgt′ (cong-∷-ren (cong-ren {Γ'' = Θ} r)))
              (trans (Tgt-cast-irr (castOf {Γ} {[ ρ ] A} (Θ ∷ C))
                                   (cong (_∷ C) (castOf {Γ} {[ ρ ] A} Θ)) _)
                     (Tgt-cast-∷ (castOf {Γ} {[ ρ ] A} Θ) _)))
    (trans (cong Tgt-∷ (rvar-hit-ren r Θ W))
      (trans (sym (Tgt-cast-∷ (castOf {Γ'} {[ ρ ] A} Θ) _))
             (Tgt-cast-irr (cong (_∷ C) (castOf {Γ'} {[ ρ ] A} Θ))
                           (castOf {Γ'} {[ ρ ] A} (Θ ∷ C)) _)))

rvar-hit-ren {Γ} {Γ'} {A} {ρ} r (Θ ⟨ ρ' ⟩) W =
  trans (cong (var-tgt′ (cong-⟨⟩-ren (cong-ren {Γ'' = Θ} r)))
              (trans (Tgt-cast-irr (castOf {Γ} {[ ρ ] A} (Θ ⟨ ρ' ⟩))
                                   (cong (_⟨ ρ' ⟩) (castOf {Γ} {[ ρ ] A} Θ)) _)
                     (Tgt-cast-⟨⟩ ρ' (castOf {Γ} {[ ρ ] A} Θ) _)))
    (trans (cong (Tgt-⟨⟩ ρ') (rvar-hit-ren r Θ W))
      (trans (sym (Tgt-cast-⟨⟩ ρ' (castOf {Γ'} {[ ρ ] A} Θ) _))
             (Tgt-cast-irr (cong (_⟨ ρ' ⟩) (castOf {Γ'} {[ ρ ] A} Θ))
                           (castOf {Γ'} {[ ρ ] A} (Θ ⟨ ρ' ⟩)) _)))

rvar-hit-ren′ : ∀ {Γ Γ' A ρ σ} → (r : Ren [] Γ Γ') → (Θ : Ctx)
              → (W : Γ ⊢V⦂ [ ρ ] A)
              → (c  : [ ρ ] A ∈[ σ ] ((Γ ∷ [ ρ ] A) ++ᶜ Θ))
              → (t' : Tgt ((Γ' ∷ [ ρ ] A) ++ᶜ Θ) ([ ρ ] A))
              → _≡_ {A = Tgt ((Γ ∷ [ ρ ] A) ++ᶜ Θ) ([ ρ ] A)}
                  (σ , c)
                  (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
              → t' ≡ (ctx-grade Θ , split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
              → var-tgt′ (cong-ren {Γ'' = Θ} r)
                  (Tgt-cast (castOf {Γ} {[ ρ ] A} Θ)
                    (rvar-tgt c (split→∈ (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))
                              (castᵛ (sym (split→∈-split-l
                                             (split-≡-++ᶜ {Γ ∷ [ ρ ] A} {Θ}))) W)))
              ≡ Tgt-cast (castOf {Γ'} {[ ρ ] A} Θ)
                  (rvar-tgt (proj₂ t')
                            (split→∈ (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ}))
                            (castᵛ (sym (split→∈-split-l
                                           (split-≡-++ᶜ {Γ' ∷ [ ρ ] A} {Θ})))
                                   (V-rename r W)))
rvar-hit-ren′ r Θ W _ _ refl refl = rvar-hit-ren r Θ W

unbox-cell-ren : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A ρ σ}
               → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B) ++ᶜ Θ)) → (W : Γ ⊢V⦂ B)
               → var-tgt′ (cong-ren {Γ'' = Θ} r)
                   (Tgt-cast (castOf {Γ} {B} Θ)
                     (rvar-tgt c (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                               (castᵛ (sym (split→∈-split-l
                                              (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
               ≡ Tgt-cast (castOf {Γ'} {B} Θ)
                   (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (cong-∷-ren r)) c))
                             (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                    (V-rename r W)))

unbox-cell-ren {Γ} {Γ'} {B} r Θ {A} {ρ} {σ} c W
  with ∈-++ᶜ-split (Γ ∷ B) Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B) Θ c c' eqc =
  trans (cong (var-tgt′ (cong-ren {Γ'' = Θ} r)) (sub-rvar-r Θ c' _))
    (trans (cong-ren-tgt-r r c')
           (sym (sub-rvar-r′ Θ c' _ (cong-ren-tgt-r (cong-∷-ren r) c') _)))

... | inj₁ (σ' , c') =
  subst (λ t → var-tgt′ (cong-ren {Γ'' = Θ} r)
                 (Tgt-cast (castOf {Γ} {B} Θ)
                   (rvar-tgt (proj₂ t) (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                             (castᵛ (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
             ≡ Tgt-cast (castOf {Γ'} {B} Θ)
                 (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                                           (proj₂ t)))
                           (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                           (castᵛ (sym (split→∈-split-l
                                          (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                                  (V-rename r W))))
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B) Θ c c' eqc))
        (go c')
  where
    go : ∀ {σ₀} → (c₀ : [ ρ ] A ∈[ σ₀ ] (Γ ∷ B))
       → var-tgt′ (cong-ren {Γ'' = Θ} r)
           (Tgt-cast (castOf {Γ} {B} Θ)
             (rvar-tgt (∈-++ᶜˡ {Γ = Γ ∷ B} Θ c₀)
                       (split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ}))
                       (castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W)))
       ≡ Tgt-cast (castOf {Γ'} {B} Θ)
           (rvar-tgt (proj₂ (var-tgt (cong-ren {Γ'' = Θ} (cong-∷-ren r))
                                     (∈-++ᶜˡ {Γ = Γ ∷ B} Θ c₀)))
                     (split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ}))
                     (castᵛ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                            (V-rename r W)))

    go Hd =
      rvar-hit-ren′ r Θ W (∈-++ᶜˡ {Γ = Γ ∷ B} Θ (Hd {Γ = Γ})) _
        (sym (split→∈-∈-++ᶜˡ Γ B Θ))
        (trans (cong-ren-tgt-l (cong-∷-ren r) Θ (Hd {Γ = Γ}))
               (sym (split→∈-∈-++ᶜˡ Γ' B Θ)))

    go (Tl-∷ c₀) =
      trans (cong (var-tgt′ (cong-ren {Γ'' = Θ} r)) (sub-rvar-l Θ c₀ _))
        (trans (cong-ren-tgt-l r Θ c₀)
               (sym (sub-rvar-l′ Θ (proj₂ (var-tgt r c₀)) _
                       (cong-ren-tgt-l (cong-∷-ren r) Θ (Tl-∷ c₀)) _)))


-- The two formers that do not simply distribute: `unbox`, whose boxed value is
-- a variable the substitution relocates, and `handle`, whose clauses see the
-- substitution only through the eternal restriction. Both are stated so that
-- the induction below can hand them its hypothesis at the grown suffix.

-- `unbox`: both orders rebuild the unboxing from the cell the substitution
-- leaves (`sub-unbox`), and `unbox-cell-ren` says the two cells agree. The body
-- is the induction hypothesis at the grown suffix, taken as an argument so that
-- this can stand outside the induction.

ren-sub-unbox
  : ∀ {Γ Γ' B A ρ C Δ} → (r : Ren [] Γ Γ') → (Θ : Ctx)
  → (w : Ren [] (Δ ⟨ ρ ⟩) ((Γ ∷ B) ++ᶜ Θ))
  → (V : Δ ⊢V⦂ [ ρ ] A)
  → (M : (((Γ ∷ B) ++ᶜ Θ) ∷ A) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
  → (ih : C-rename (cong-ren {Γ'' = Θ ∷ A} r)
            (castᶜ (castOf {Γ} {B} (Θ ∷ A))
              (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ ∷ A})
                   ↦ castᵛ (sym (split→∈-split-l
                                   (split-≡-++ᶜ {Γ ∷ B} {Θ ∷ A}))) W ]c))
          ≐ᶜ castᶜ (castOf {Γ'} {B} (Θ ∷ A))
               ((C-rename (cong-ren {Γ'' = Θ ∷ A} (cong-∷-ren r)) M)
                  [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ ∷ A})
                    ↦ castᵛ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ' ∷ B} {Θ ∷ A})))
                            (V-rename r W) ]c))
  → C-rename (cong-ren {Γ'' = Θ} r)
      (castᶜ (castOf {Γ} {B} Θ)
        (unbox w V M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
  ≐ᶜ castᶜ (castOf {Γ'} {B} Θ)
       ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) (unbox w V M))
          [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
            ↦ castᵛ (sym (split→∈-split-l
                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                    (V-rename r W) ]c)

ren-sub-unbox {Γ} {Γ'} {B} {A} {ρ} r Θ w V M W ih =
  ≐ᶜ-trans
    (C-rename-cong ρ₀
      (≐ᶜ-trans (castᶜ-≐ (castOf {Γ} {B} Θ) (sub-unbox w V M xL WL relL))
                (≡→≐ᶜ (cast-unbox (castOf {Γ} {B} Θ)))))
    (≐ᶜ-trans
      (unbox-≐ cell
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A} r))
                      (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ∷ A)) _)))
          (≐ᶜ-trans ih
                    (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A))
                                     (cong (_∷ A) (castOf {Γ'} {B} Θ)) _)))))
      (≐ᶜ-sym
        (≐ᶜ-trans (castᶜ-≐ (castOf {Γ'} {B} Θ)
                    (sub-unbox (ρ' ∘ʳ w) V (C-rename (cong-∷-ren ρ') M)
                               xR WR relR))
                  (≡→≐ᶜ (cast-unbox (castOf {Γ'} {B} Θ))))))
  where
    ρ₀ = cong-ren {Γ'' = Θ} r
    ρ' = cong-ren {Γ'' = Θ} (cong-∷-ren r)

    xL = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    xR = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
    WL = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W
    WR = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))) (V-rename r W)

    cL = proj₂ (unbox-tgt w V)

    relL = ≾ᵣ-trans (proj₂ (proj₂ (⟨ cL ⟩[ xL ↦ WL ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var w V)))

    relR = ≾ᵣ-trans
             (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt (ρ' ∘ʳ w) V) ⟩[ xR ↦ WR ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (ρ' ∘ʳ w) V)))

    hd : ∀ {Γ₀ : Ctx} → (Γ₀ ∷ [ ρ ] A) ⊢V⦂ [ ρ ] A
    hd = var (λ _ → ≾ᵣ-refl) Hd

    vL = proj₂ (rvar-tgt cL xL WL)
    vR = proj₂ (rvar-tgt (proj₂ (unbox-tgt (ρ' ∘ʳ w) V)) xR WR)

    wL = castʳᵉ (castOf {Γ} {B} Θ) (unbox-var-ren vL relL)
    wR = castʳᵉ (castOf {Γ'} {B} Θ) (unbox-var-ren vR relR)

    cell : unbox-tgt (ρ₀ ∘ʳ wL) hd ≡ unbox-tgt wR hd
    cell =
      trans (unbox-tgt-∘ ρ₀ wL hd)
        (trans (cong (var-tgt′ ρ₀)
                 (trans (unbox-tgt-castʳᵉ (castOf {Γ} {B} Θ)
                                          (unbox-var-ren vL relL) hd)
                        (cong (Tgt-cast (castOf {Γ} {B} Θ))
                              (unbox-var-tgt vL relL))))
          (trans (unbox-cell-ren r Θ cL W)
            (trans (cong (λ t → Tgt-cast (castOf {Γ'} {B} Θ)
                                  (rvar-tgt (proj₂ t) xR WR))
                         (sym (unbox-tgt-∘ ρ' w V)))
              (sym (trans (unbox-tgt-castʳᵉ (castOf {Γ'} {B} Θ)
                                            (unbox-var-ren vR relR) hd)
                     (cong (Tgt-cast (castOf {Γ'} {B} Θ))
                           (unbox-var-tgt vR relR)))))))

------------------------------------------------------------------------
-- RESTRICTING A SUFFIX-EXTENDED RENAMING
--
-- `restrict-ren (cong-ren {Δ} r)` is `cong-ren {Δ ᴱ} (restrict-ren r)`,
-- conjugated by `eq-ren`s at `ᴱ`'s distribution over `_++ᶜ_` — the
-- arbitrary-prefix-renaming counterpart of `restrict-wk-et-≐`.
------------------------------------------------------------------------

restrict-cong-≐ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (Δ : Ctx)
                → (e₁ : (Γ ++ᶜ Δ) ᴱ ≡ Γ ᴱ ++ᶜ Δ ᴱ)
                → (e₂ : (Γ' ++ᶜ Δ) ᴱ ≡ Γ' ᴱ ++ᶜ Δ ᴱ)
                → restrict-ren {Ξ = []} (cong-ren {Γ'' = Δ} r)
                ≐ʳ (eq-ren (sym e₂)
                    ∘ʳ cong-ren {Γ'' = Δ ᴱ} (restrict-ren r) ∘ʳ eq-ren e₁)

restrict-cong-≐ r [] e₁ e₂
  rewrite uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

restrict-cong-≐ r (Δ ∷ C) e₁ e₂ with eternal? C

... | yes _ =
  ≐ʳ-trans (cong-∷-ren-≐ (restrict-cong-≐ r Δ (∷ᶜ-injective-ctx e₁)
                                              (∷ᶜ-injective-ctx e₂)))
    (≐ʳ-trans (cong-∷-ren-∘-≐ _ _)
      (≐ʳ-trans (∘ʳ-≐ (≐ʳ-sym (eq-ren-∷-≐ (sym (∷ᶜ-injective-ctx e₂))))
                      (cong-∷-ren-∘-≐ _ _))
        (≐ʳ-trans (∘ʳ-≐ (eq-ren-≐ _ (sym e₂))
                        (∘ʳ-≐ ≐ʳ-refl
                              (≐ʳ-sym (eq-ren-∷-≐ (∷ᶜ-injective-ctx e₁)))))
                  (∘ʳ-≐ ≐ʳ-refl (∘ʳ-≐ ≐ʳ-refl (eq-ren-≐ _ e₁))))))

... | no  _ = restrict-cong-≐ r Δ e₁ e₂

restrict-cong-≐ r (Δ ⟨ ρ ⟩) e₁ e₂ = restrict-cong-≐ r Δ e₁ e₂

-- Restricting a binder extension: at an eternal binder the restriction
-- keeps it, at a non-eternal one it drops it — in both cases conjugated
-- by `eq-ren`s at the (only propositional) context equalities.

restrict-∷-et-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (et : Eternal B)
                → (e₁ : (Γ ∷ B) ᴱ ≡ Γ ᴱ ∷ B)
                → (e₂ : (Γ' ∷ B) ᴱ ≡ Γ' ᴱ ∷ B)
                → restrict-ren {Ξ = []} (cong-∷-ren {A = B} r)
                ≐ʳ (eq-ren (sym e₂)
                    ∘ʳ cong-∷-ren {A = B} (restrict-ren r) ∘ʳ eq-ren e₁)

restrict-∷-et-≐ r et e₁ e₂
  rewrite eternal?-yes et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

restrict-∷-ne-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (¬et : ¬ Eternal B)
                → (e₁ : (Γ ∷ B) ᴱ ≡ Γ ᴱ)
                → (e₂ : (Γ' ∷ B) ᴱ ≡ Γ' ᴱ)
                → restrict-ren {Ξ = []} (cong-∷-ren {A = B} r)
                ≐ʳ (eq-ren (sym e₂) ∘ʳ restrict-ren r ∘ʳ eq-ren e₁)

restrict-∷-ne-≐ r ¬et e₁ e₂
  rewrite eternal?-no ¬et
        | uip {p = e₁} {q = refl} | uip {p = e₂} {q = refl} =
  ≐ʳ-sym (≐ʳ-trans (∘ʳ-identityˡ-≐ _) (∘ʳ-identityʳ-≐ _))

------------------------------------------------------------------------
-- SPLITTING UNIQUENESS ACROSS TRANSPORTED HALVES
--
-- `split→∈-unique` requires the two splittings' halves to agree on the
-- nose; here they agree only propositionally, so the halves' equations
-- are matched first and the grade transport rides along.
------------------------------------------------------------------------

split→∈-unique₂ : ∀ {Γ Γ' Γ₁ Γ₁' Γ₂ Γ₂' A}
                → (eΓ₁ : Γ₁ ≡ Γ₁') → (eΓ₂ : Γ₂ ≡ Γ₂') → (e : Γ ≡ Γ')
                → (s : Γ₁ ∷ A , Γ₂ split Γ) → (s' : Γ₁' ∷ A , Γ₂' split Γ')
                → subst (λ Γ₀ → A ∈[ ctx-grade Γ₂' ] Γ₀) e
                    (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) (cong ctx-grade eΓ₂)
                           (split→∈ s))
                ≡ split→∈ s'
split→∈-unique₂ refl refl e s s' = split→∈-unique e s s'

-- The two halves' equations induced by a grade-and-context transport of
-- the substituted variable.

sl-eq : ∀ {Γ Γ' A ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
      → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
      → subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y
      → split-l x ≡ split-l y
sl-eq refl e x y ey = trans (split-l-cast e x) (cong split-l ey)

sr-eq : ∀ {Γ Γ' A ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
      → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
      → subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y
      → split-r x ≡ split-r y
sr-eq refl e x y ey = trans (split-r-cast e x) (cong split-r ey)

-- `sub-cast-C′` with the substituted variable's grade transported too.

sub-cast-C″ : ∀ {Γ Γ' A C ρ ρ'} → (eρ : ρ ≡ ρ') → (e : Γ ≡ Γ')
            → (M : Γ ⊢C⦂ C)
            → (x : A ∈[ ρ ] Γ) → (y : A ∈[ ρ' ] Γ')
            → (ey : subst (λ Γ₀ → A ∈[ ρ' ] Γ₀) e
                          (subst (λ ρ₀ → A ∈[ ρ₀ ] Γ) eρ x) ≡ y)
            → (U : split-l x ⊢V⦂ A) → (U' : split-l y ⊢V⦂ A)
            → (eU : subst (_⊢V⦂ A) (sl-eq eρ e x y ey) U ≡ U')
            → (subst (_⊢C⦂ C) e M) [ y ↦ U' ]c
            ≡ subst (_⊢C⦂ C) (cong₂ _++ᶜ_ (sl-eq eρ e x y ey)
                                          (sr-eq eρ e x y ey))
                (M [ x ↦ U ]c)
sub-cast-C″ refl e M x y ey U U' eU = sub-cast-C′ e M x y ey U U' eU

------------------------------------------------------------------------
-- VALUE-LEVEL TRANSPORT ALGEBRA
------------------------------------------------------------------------

castᵛ≡subst : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
            → castᵛ e V ≡ subst (_⊢V⦂ A) e V
castᵛ≡subst refl V = refl

subst-fuseᵛ : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (V : Γ₁ ⊢V⦂ A)
            → subst (_⊢V⦂ A) e' (subst (_⊢V⦂ A) e V)
            ≡ subst (_⊢V⦂ A) (trans e e') V
subst-fuseᵛ refl refl V = refl

-- Two transport chains out of the same value agree by `uip`.

substᵛ-irr : ∀ {Γ Γ' A} → (e e' : Γ ≡ Γ') → (V : Γ ⊢V⦂ A)
           → subst (_⊢V⦂ A) e V ≡ subst (_⊢V⦂ A) e' V
substᵛ-irr e e' V = cong (λ z → subst (_⊢V⦂ _) z V) (uip {p = e} {q = e'})

-- The eternal restriction of a value respects a context transport.

restrict-castᵛ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → (et : Eternal A) → (V : Γ ⊢V⦂ A)
               → eternal-val-restrict et (castᵛ e V)
               ≡ castᵛ (cong _ᴱ e) (eternal-val-restrict et V)
restrict-castᵛ refl et V = refl

------------------------------------------------------------------------
-- THE ETERNAL RESTRICTION IS NATURAL IN RENAMING
--
-- The var case goes through the reflection `∈-ᴱ⁻`: both sides' targets
-- reflect to `var-tgt r x`, so `∈-ᴱ⁻-inj` identifies them.
------------------------------------------------------------------------

eternal-val-restrict-ren : ∀ {Γ Γ' A} → (et : Eternal A)
                         → (r : Ren [] Γ Γ') → (W : Γ ⊢V⦂ A)
                         → eternal-val-restrict et (V-rename r W)
                         ≐ᵛ V-rename (restrict-ren r) (eternal-val-restrict et W)

eternal-val-restrict-ren {Γ} {Γ'} et r (var f x) =
  ≐ᵛ-trans
    (eternal-val-restrict-cong et (var-ren-≐ r x f fet))
    (≐ᵛ-sym (var-ren-tgt-≐ (restrict-ren r) (∈-ᴱ et x) fet
                           (sym tgt-eq) fet))
  where
    fet : ∀ {ρ₀} → ¬ Eternal _ → ρ₀ ≾ᵣ uᵣ
    fet ¬et = ⊥-elim (¬et et)

    tgt-eq : _≡_ {A = Tgt (Γ' ᴱ) _}
                 (uᵣ , ∈-ᴱ et (proj₂ (var-tgt r x)))
                 (var-tgt (restrict-ren r) (∈-ᴱ et x))
    tgt-eq =
      ∈-ᴱ⁻-inj Γ' _ _
        (trans (∈-ᴱ⁻-∈-ᴱ Γ' et (proj₂ (var-tgt r x)))
          (sym (trans (restrict-tgt⁻ r (∈-ᴱ et x))
                      (cong (var-tgt′ r) (∈-ᴱ⁻-∈-ᴱ Γ et x)))))

eternal-val-restrict-ren et r (const c) = ≐ᵛ-refl _
eternal-val-restrict-ren et r ⋆         = ≐ᵛ-refl _
eternal-val-restrict-ren (et₁ |×|ₑ et₂) r ⦉ V₁ , V₂ ⦊ =
  pair-≐ (eternal-val-restrict-ren et₁ r V₁)
         (eternal-val-restrict-ren et₂ r V₂)

------------------------------------------------------------------------
-- THE `ren-sub` STATEMENT, ABBREVIATED
------------------------------------------------------------------------

RenSubC : ∀ {Γ Γ' B C} → Ren [] Γ Γ' → (Θ : Ctx)
        → ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ ⊢V⦂ B → Set
RenSubC {Γ} {Γ'} {B} r Θ M W =
  C-rename (cong-ren {Γ'' = Θ} r)
      (castᶜ (castOf {Γ} {B} Θ)
        (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
             ↦ castᵛ (sym (split→∈-split-l
                             (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
  ≐ᶜ castᶜ (castOf {Γ'} {B} Θ)
       ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
          [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
            ↦ castᵛ (sym (split→∈-split-l
                            (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                    (V-rename r W) ]c)

-- A clause's two binders, as a suffix.

Dcl : VType → Op → E → Ctx
Dcl D op ε'' =
  [] ∷ type-of-gtype (param op)
     ∷ [ mapᵉ (op-grade op) ] (type-of-gtype (arity op) ⇒ D ‼ ε'')

-- The clause context, relocated to the recursion's canonical contexts.

ren-sub-eTot : ∀ {Γ B} → (Θ : Ctx) → Eternal B → (Δ : Ctx)
             → ((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ Δ ≡ (Γ ᴱ ∷ B) ++ᶜ (Θ ᴱ ++ᶜ Δ)
ren-sub-eTot {Γ} {B} Θ et Δ =
  trans (cong (_++ᶜ Δ)
              (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                     (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))))
        (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) Δ)

------------------------------------------------------------------------
-- CONJUGATED DECOMPOSITIONS
--
-- Every renaming this proof decomposes comes out as an `eq-ren`-conjugated
-- core; the two helpers below fuse nested conjugations and turn a
-- conjugation into transports around the core's action.
------------------------------------------------------------------------

infix 4 _≐ʳconj⟨_,_,_⟩

_≐ʳconj⟨_,_,_⟩ : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → Ren [] Γ₁ Γ₂'
              → (Γ₁ ≡ Γ₁') → Ren [] Γ₁' Γ₂ → (Γ₂ ≡ Γ₂') → Set
R ≐ʳconj⟨ e , K , e' ⟩ = R ≐ʳ (eq-ren e' ∘ʳ K ∘ʳ eq-ren e)

-- Fusing a conjugation of a conjugation.

conj-fuse : ∀ {Γ₁ Γ₀ Γ₀' Γ₂ Γ₂' Γ₃}
          → {R : Ren [] Γ₀ Γ₂'} → (a : Γ₁ ≡ Γ₀) → (a' : Γ₂' ≡ Γ₃)
          → {K : Ren [] Γ₀' Γ₂} → (b : Γ₀ ≡ Γ₀') → (b' : Γ₂ ≡ Γ₂')
          → R ≐ʳconj⟨ b , K , b' ⟩
          → (eq-ren a' ∘ʳ R ∘ʳ eq-ren a) ≐ʳconj⟨ trans a b , K , trans b' a' ⟩
conj-fuse {R = R} a a' {K = K} b b' h =
  ≐ʳ-trans (∘ʳ-≐ ≐ʳ-refl (∘ʳ-≐ h ≐ʳ-refl))
    (≐ʳ-trans
      (∘ʳ-≐ ≐ʳ-refl (≐ʳ-trans (∘ʳ-assoc-≐ _ _ _)
                              (∘ʳ-≐ ≐ʳ-refl
                                (≐ʳ-trans (∘ʳ-assoc-≐ _ _ _)
                                          (∘ʳ-≐ ≐ʳ-refl (eq-ren-∘-≐ a b))))))
      (≐ʳ-trans (≐ʳ-sym (∘ʳ-assoc-≐ _ _ _))
                (∘ʳ-≐ (eq-ren-∘-≐ b' a') ≐ʳ-refl)))

-- Extending a conjugation by a suffix.

conj-cong-ren : ∀ {Γ₁ Γ₁' Γ₂ Γ₂'} → (Δ : Ctx)
              → {R : Ren [] Γ₁ Γ₂'} → (e : Γ₁ ≡ Γ₁')
              → {K : Ren [] Γ₁' Γ₂} → (e' : Γ₂ ≡ Γ₂')
              → R ≐ʳconj⟨ e , K , e' ⟩
              → cong-ren {Γ'' = Δ} R
                  ≐ʳconj⟨ cong (_++ᶜ Δ) e , cong-ren {Γ'' = Δ} K
                        , cong (_++ᶜ Δ) e' ⟩
conj-cong-ren Δ e e' h =
  ≐ʳ-trans (cong-ren-≐ Δ h)
    (≐ʳ-trans (cong-ren-∘-≐ Δ _ _)
      (∘ʳ-≐ (cong-ren-eq-ren-≐ Δ e')
            (≐ʳ-trans (cong-ren-∘-≐ Δ _ _)
                      (∘ʳ-≐ ≐ʳ-refl (cong-ren-eq-ren-≐ Δ e)))))

-- The action of a conjugated renaming is the core's action between the
-- two transports.

C-rename-conj : ∀ {Γ₁ Γ₁' Γ₂ Γ₂' C}
              → {R : Ren [] Γ₁ Γ₂'} → (e : Γ₁ ≡ Γ₁')
              → {K : Ren [] Γ₁' Γ₂} → (e' : Γ₂ ≡ Γ₂')
              → R ≐ʳconj⟨ e , K , e' ⟩
              → (X : Γ₁ ⊢C⦂ C)
              → C-rename R X
              ≐ᶜ subst (_⊢C⦂ C) e' (C-rename K (subst (_⊢C⦂ C) e X))
C-rename-conj e {K = K} e' h X =
  ≐ᶜ-trans (C-rename-≐ h X)
    (≐ᶜ-trans (C-rename-∘ (eq-ren e') (K ∘ʳ eq-ren e) X)
      (≐ᶜ-trans
        (C-rename-eq-≐ e' ≐ʳ-refl (C-rename (K ∘ʳ eq-ren e) X))
        (substᶜ-≐ e'
          (≐ᶜ-trans (C-rename-∘ K (eq-ren e) X)
                    (C-rename-cong K (C-rename-eq-≐ e ≐ʳ-refl X))))))

------------------------------------------------------------------------
-- THE TWO CLAUSE RENAMINGS, DECOMPOSED
--
-- Both sides of `ren-sub-handle`'s clause comparison rename by
-- `cong-ren {D}` of a restriction of a suffix-extended renaming; both
-- decompose onto the same core over the canonical restricted contexts.
------------------------------------------------------------------------

-- The left side: `restrict-ren (cong-ren {Θ} r)`, extended by the two
-- clause binders.

clause-ren-l-≐ : ∀ {Γ Γ'} → (r : Ren [] Γ Γ') → (Θ Δ : Ctx)
               → cong-ren {Γ'' = Δ}
                   (restrict-ren {Ξ = []} (cong-ren {Γ'' = Θ} r))
               ≐ʳconj⟨ trans (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ Θ))
                             (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                     , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ} (restrict-ren {Ξ = []} r)
                     , sym (trans (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ' Θ))
                                  (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ)) ⟩
clause-ren-l-≐ {Γ} {Γ'} r Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ (ᴱ-++ᶜ Γ Θ) (sym (ᴱ-++ᶜ Γ' Θ))
       (restrict-cong-≐ r Θ (ᴱ-++ᶜ Γ Θ) (ᴱ-++ᶜ Γ' Θ)))
    (≐ʳ-trans
      (conj-fuse (cong (_++ᶜ Δ) (ᴱ-++ᶜ Γ Θ))
                 (cong (_++ᶜ Δ) (sym (ᴱ-++ᶜ Γ' Θ)))
                 (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                 (sym (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ))
                 (cong-ren-assoc-≐ (Θ ᴱ) Δ (restrict-ren {Ξ = []} r)))
      (∘ʳ-≐ (eq-ren-≐ _ _) ≐ʳ-refl))

-- The right side: `restrict-ren (cong-ren {Θ} (cong-∷-ren r))` at an
-- eternal substituted type — the restriction keeps the binder.

clause-ren-r-et-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (et : Eternal B)
                  → (Θ Δ : Ctx)
                  → cong-ren {Γ'' = Δ}
                      (restrict-ren {Ξ = []}
                        (cong-ren {Γ'' = Θ} (cong-∷-ren {A = B} r)))
                  ≐ʳconj⟨ ren-sub-eTot {Γ} {B} Θ et Δ
                        , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ}
                            (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))
                        , sym (ren-sub-eTot {Γ'} {B} Θ et Δ) ⟩
clause-ren-r-et-≐ {Γ} {Γ'} {B} r et Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ _ _
      (≐ʳ-trans
        (restrict-cong-≐ (cong-∷-ren {A = B} r) Θ
           (ᴱ-++ᶜ (Γ ∷ B) Θ) (ᴱ-++ᶜ (Γ' ∷ B) Θ))
        (conj-fuse (ᴱ-++ᶜ (Γ ∷ B) Θ) (sym (ᴱ-++ᶜ (Γ' ∷ B) Θ))
           (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et))
           (cong (_++ᶜ Θ ᴱ) (sym (ᴱ-∷-keep {Γ'} {B} et)))
           (conj-cong-ren (Θ ᴱ) (ᴱ-∷-keep {Γ} {B} et)
              (sym (ᴱ-∷-keep {Γ'} {B} et))
              (restrict-∷-et-≐ r et (ᴱ-∷-keep {Γ} {B} et)
                                    (ᴱ-∷-keep {Γ'} {B} et))))))
    (≐ʳ-trans
      (conj-fuse _ _
         (++ᶜ-assoc (Γ ᴱ ∷ B) (Θ ᴱ) Δ)
         (sym (++ᶜ-assoc (Γ' ᴱ ∷ B) (Θ ᴱ) Δ))
         (cong-ren-assoc-≐ (Θ ᴱ) Δ (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))))
      (∘ʳ-≐ (eq-ren-≐ _ _) ≐ʳ-refl))

-- The same at a non-eternal substituted type — the restriction drops it.

clause-ren-r-ne-≐ : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (¬et : ¬ Eternal B)
                  → (Θ Δ : Ctx)
                  → cong-ren {Γ'' = Δ}
                      (restrict-ren {Ξ = []}
                        (cong-ren {Γ'' = Θ} (cong-∷-ren {A = B} r)))
                  ≐ʳconj⟨ trans (cong (_++ᶜ Δ)
                                  (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                                    (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))))
                                (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
                        , cong-ren {Γ'' = Θ ᴱ ++ᶜ Δ} (restrict-ren {Ξ = []} r)
                        , sym (trans (cong (_++ᶜ Δ)
                                       (trans (ᴱ-++ᶜ (Γ' ∷ B) Θ)
                                         (cong (_++ᶜ Θ ᴱ)
                                               (ᴱ-∷-drop {Γ'} {B} ¬et))))
                                     (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ)) ⟩
clause-ren-r-ne-≐ {Γ} {Γ'} {B} r ¬et Θ Δ =
  ≐ʳ-trans
    (conj-cong-ren Δ _ _
      (≐ʳ-trans
        (restrict-cong-≐ (cong-∷-ren {A = B} r) Θ
           (ᴱ-++ᶜ (Γ ∷ B) Θ) (ᴱ-++ᶜ (Γ' ∷ B) Θ))
        (conj-fuse (ᴱ-++ᶜ (Γ ∷ B) Θ) (sym (ᴱ-++ᶜ (Γ' ∷ B) Θ))
           (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))
           (cong (_++ᶜ Θ ᴱ) (sym (ᴱ-∷-drop {Γ'} {B} ¬et)))
           (conj-cong-ren (Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et)
              (sym (ᴱ-∷-drop {Γ'} {B} ¬et))
              (restrict-∷-ne-≐ r ¬et (ᴱ-∷-drop {Γ} {B} ¬et)
                                     (ᴱ-∷-drop {Γ'} {B} ¬et))))))
    (≐ʳ-trans
      (conj-fuse _ _
         (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) Δ)
         (sym (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) Δ))
         (cong-ren-assoc-≐ (Θ ᴱ) Δ (restrict-ren {Ξ = []} r)))
      (∘ʳ-≐ (eq-ren-≐ _ _) ≐ʳ-refl))

------------------------------------------------------------------------
-- `handle`, NON-ETERNAL
--
-- Both sides' clause components are the same core renaming
-- `cong-ren {Θ ᴱ ++ᶜ D₀} (restrict-ren r)` of the clause, inside
-- transport chains with the same endpoints, so after both are decomposed
-- (`clause-ren-l-≐`/`clause-ren-r-ne-≐`) `uip` closes the comparison.
------------------------------------------------------------------------

ren-sub-handle-ne : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
                  → (¬et : ¬ Eternal B)
                  → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                  → (H : (op : Op) → (ε'' : E) →
                           ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                           ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                  → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                  → (W : Γ ⊢V⦂ B)
                  → (hM : RenSubC r Θ M W)
                  → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                  → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle-ne {Γ} {Γ'} {B} {A} {B'} {ε} r Θ ¬et M H N W hM hN
  rewrite eternal?-no ¬et =
  ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                       (cast-handle (castOf {Γ} {B} Θ))))
    (≐ᶜ-trans
      (handle-≐ hM (λ op ε'' → clause op ε'')
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                      (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
          (≐ᶜ-trans hN
            (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                             (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                   (castOf {Γ'} {B} Θ)) _)))))
      (≡→≐ᶜ (sym (cast-handle (castOf {Γ'} {B} Θ)))))
  where
    z₀  = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    z₀' = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

    clause : (op : Op) → (ε'' : E) → _
    clause op ε'' =
      ≐ᶜ-trans
        (C-rename-conj eLL eLL' (clause-ren-l-≐ r Θ D₀) _)
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (λ z → subst (_⊢C⦂ CT) eLL' (C-rename K z)) inner-eq))
          (≐ᶜ-trans
            (≡→≐ᶜ uip²)
            (≐ᶜ-sym
              (≐ᶜ-trans (≡→≐ᶜ r1)
                (≐ᶜ-trans
                  (substᶜ-≐ TRout
                    (C-rename-conj eRR eRR'
                       (clause-ren-r-ne-≐ r ¬et Θ D₀) (H op ε'')))
                  (≡→≐ᶜ (subst-fuseᶜ eRR' TRout _)))))))
      where
        D₀ = [] ∷ type-of-gtype (param op)
                ∷ [ mapᵉ (op-grade op) ]
                    (type-of-gtype (arity op) ⇒ B' ‼ ε'')

        CT = B' ‼ (op-grade op ·ₑ ε'')

        K = cong-ren {Γ'' = Θ ᴱ ++ᶜ D₀} (restrict-ren {Ξ = []} r)

        cDL = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ} {B} Θ)

        cDR = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ'} {B} Θ)

        eLL = trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ Θ)) (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eLL' = sym (trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ' Θ))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        eRR = trans (cong (_++ᶜ D₀)
                          (trans (ᴱ-++ᶜ (Γ ∷ B) Θ)
                                 (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {Γ} {B} ¬et))))
                    (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eRR' = sym (trans (cong (_++ᶜ D₀)
                                (trans (ᴱ-++ᶜ (Γ' ∷ B) Θ)
                                       (cong (_++ᶜ Θ ᴱ)
                                             (ᴱ-∷-drop {Γ'} {B} ¬et))))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        dropL = ᴱ-drop-split ¬et z₀
        dropR = ᴱ-drop-split ¬et z₀'

        TL = trans (trans (cong (_++ᶜ D₀) dropL) cDL) eLL

        TRout = trans (cong (_++ᶜ D₀) dropR) cDR

        inner-eq : subst (_⊢C⦂ CT) eLL
                     (castᶜ cDL
                       (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                        ∷ [ mapᵉ (op-grade op) ]
                                            (type-of-gtype (arity op)
                                              ⇒ B' ‼ ε'')
                                      ⊢C⦂ CT)
                              dropL (H op ε'')))
                 ≡ subst (_⊢C⦂ CT) TL (H op ε'')
        inner-eq =
          trans (cong (subst (_⊢C⦂ CT) eLL)
                   (trans (cong (castᶜ cDL)
                                (subst-++ᶜʳ D₀ dropL (H op ε'')))
                     (trans (castᶜ≡subst cDL _)
                            (subst-fuseᶜ (cong (_++ᶜ D₀) dropL) cDL
                                         (H op ε'')))))
                (subst-fuseᶜ (trans (cong (_++ᶜ D₀) dropL) cDL) eLL (H op ε''))

        r1 : castᶜ cDR
               (subst (λ Γ₀ → Γ₀ ∷ type-of-gtype (param op)
                                ∷ [ mapᵉ (op-grade op) ]
                                    (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                              ⊢C⦂ CT)
                      dropR
                      (C-rename (cong-∷-ren (cong-∷-ren
                                  (restrict-ren {Ξ = []}
                                    (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                                (H op ε'')))
           ≡ subst (_⊢C⦂ CT) TRout
               (C-rename (cong-∷-ren (cong-∷-ren
                           (restrict-ren {Ξ = []}
                             (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                         (H op ε''))
        r1 =
          trans (cong (castᶜ cDR) (subst-++ᶜʳ D₀ dropR _))
            (trans (castᶜ≡subst cDR _)
                   (subst-fuseᶜ (cong (_++ᶜ D₀) dropR) cDR _))

        uip² : subst (_⊢C⦂ CT) eLL'
                 (C-rename K (subst (_⊢C⦂ CT) TL (H op ε'')))
             ≡ subst (_⊢C⦂ CT) (trans eRR' TRout)
                 (C-rename K (subst (_⊢C⦂ CT) eRR (H op ε'')))
        uip² =
          trans (cong (λ p → subst (_⊢C⦂ CT) eLL'
                               (C-rename K (subst (_⊢C⦂ CT) p (H op ε''))))
                      (uip {p = TL} {q = eRR}))
                (cong (λ p → subst (_⊢C⦂ CT) p
                               (C-rename K (subst (_⊢C⦂ CT) eRR (H op ε''))))
                      (uip {p = eLL'} {q = trans eRR' TRout}))

------------------------------------------------------------------------
-- `handle`, ETERNAL
--
-- The clause substitutes the restricted value, so the comparison is the
-- recursion (`hH`, `ren-sub-C` at the canonical restricted contexts) with
-- the goal's two substitutions carried over by `sub-cast-C″` — the
-- splittings' halves agree with the canonical ones only propositionally,
-- which `split→∈-unique₂` absorbs — and the value mismatch bridged by
-- `eternal-val-restrict-ren`.
------------------------------------------------------------------------

ren-sub-handle-et : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
                  → (et : Eternal B)
                  → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                  → (H : (op : Op) → (ε'' : E) →
                           ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                           ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                  → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
                  → (W : Γ ⊢V⦂ B)
                  → (hM : RenSubC r Θ M W)
                  → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                  → (hH : (op : Op) → (ε'' : E)
                        → RenSubC {Γ ᴱ} {Γ' ᴱ} {B}
                            (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                            (subst (_⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                                   (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                                   (H op ε''))
                            (eternal-val-restrict et W))
                  → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle-et {Γ} {Γ'} {B} {A} {B'} {ε} r Θ et M H N W hM hN hH =
  ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                       (cast-handle (castOf {Γ} {B} Θ))))
    (≐ᶜ-trans
      (handle-≐ hM (λ op ε'' → clause op ε'')
        (≐ᶜ-trans
          (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                      (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                       (castOf {Γ} {B} Θ))
                                 (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
          (≐ᶜ-trans hN
            (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                             (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                   (castOf {Γ'} {B} Θ)) _)))))
      (≡→≐ᶜ (sym (cast-handle (castOf {Γ'} {B} Θ)))))
  where
    z₀  = split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
    z₀' = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

    cWL = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))
    cWR = sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))

    clause : (op : Op) → (ε'' : E) → _
    clause op ε'' =
      ≐ᶜ-trans
        (≡→≐ᶜ (cong (λ d → C-rename
                             (cong-∷-ren (cong-∷-ren
                               (restrict-ren {Ξ = []}
                                 (cong-ren {Γ'' = Θ} r))))
                             (castᶜ cDL
                               (⟨ d ⟩[ z₀ ↦ castᵛ cWL W ]cl H op ε'')))
                    (eternal?-yes et)))
        (≐ᶜ-trans
          (C-rename-conj eLL eLL' (clause-ren-l-≐ r Θ D₀) _)
          (≐ᶜ-trans
            (≡→≐ᶜ (cong (λ z → subst (_⊢C⦂ CT) eLL' (C-rename KL z))
                        inner-eq-L))
            (≐ᶜ-trans
              (substᶜ-≐ eLL' (hH op ε''))
              (≐ᶜ-trans (≡→≐ᶜ out-eq)
                (≐ᶜ-sym
                  (≐ᶜ-trans
                    (≡→≐ᶜ (cong (λ d → castᶜ cDR
                                         (⟨ d ⟩[ z₀'
                                               ↦ castᵛ cWR (V-rename r W)
                                               ]cl
                                            (λ op₁ ε₁ →
                                               C-rename
                                                 (cong-∷-ren (cong-∷-ren
                                                   (restrict-ren {Ξ = []}
                                                     (cong-ren {Γ'' = Θ}
                                                       (cong-∷-ren r)))))
                                                 (H op₁ ε₁))
                                            op ε''))
                                (eternal?-yes et)))
                    gr-chain))))))
      where
        D₀ = Dcl B' op ε''

        CT = B' ‼ (op-grade op ·ₑ ε'')

        Θ₀ = Θ ᴱ ++ᶜ D₀

        KL = cong-ren {Γ'' = Θ₀} (restrict-ren {Ξ = []} r)
        KR = cong-ren {Γ'' = Θ₀} (cong-∷-ren {A = B} (restrict-ren {Ξ = []} r))

        eT   = ren-sub-eTot {Γ} {B} Θ et D₀
        eTΓ' = ren-sub-eTot {Γ'} {B} Θ et D₀

        Ĥ  = H op ε''
        H⁺ = subst (_⊢C⦂ CT) eT Ĥ

        sL = split-++ʳ (∈-ᴱ-split et z₀) D₀
        sR = split-++ʳ (∈-ᴱ-split et z₀') D₀

        xL = split→∈ sL
        xR = split→∈ sR

        y₁ = split→∈ (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})
        y₂ = split→∈ (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})

        VL = subst (_⊢V⦂ B) (sym (split→∈-split-l sL))
                   (eternal-val-restrict et (castᵛ cWL W))
        VR = subst (_⊢V⦂ B) (sym (split→∈-split-l sR))
                   (eternal-val-restrict et (castᵛ cWR (V-rename r W)))

        U₁ = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                   (eternal-val-restrict et W)
        U₂ = castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                   (V-rename (restrict-ren {Ξ = []} r)
                             (eternal-val-restrict et W))

        cDL = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ} {B} Θ)

        cDR = cong (λ Γ₁ → Γ₁ ᴱ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B' ‼ ε''))
                   (castOf {Γ'} {B} Θ)

        eLL = trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ Θ)) (++ᶜ-assoc (Γ ᴱ) (Θ ᴱ) D₀)

        eLL' = sym (trans (cong (_++ᶜ D₀) (ᴱ-++ᶜ Γ' Θ))
                          (++ᶜ-assoc (Γ' ᴱ) (Θ ᴱ) D₀))

        bigEL = trans (cong₂ _++ᶜ_ (split→∈-split-l sL) (split→∈-split-r sL))
                  (trans (sym (++ᶜ-assoc ((split-l z₀) ᴱ) ((split-r z₀) ᴱ) D₀))
                         (cong (_++ᶜ D₀)
                               (sym (ᴱ-++ᶜ (split-l z₀) (split-r z₀)))))

        bigER = trans (cong₂ _++ᶜ_ (split→∈-split-l sR) (split→∈-split-r sR))
                  (trans (sym (++ᶜ-assoc ((split-l z₀') ᴱ) ((split-r z₀') ᴱ) D₀))
                         (cong (_++ᶜ D₀)
                               (sym (ᴱ-++ᶜ (split-l z₀') (split-r z₀')))))

        -- the left substitution, carried to the canonical contexts

        eΓ₁L = cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B} {Θ}))
        eΓ₂L = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D₀)
                    (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B} {Θ}))

        eρL = cong ctx-grade eΓ₂L

        eyL : subst (λ Γ₀ → B ∈[ ctx-grade Θ₀ ] Γ₀) eT
                (subst (λ ρ₀ → B ∈[ ρ₀ ] (((Γ ∷ B) ++ᶜ Θ) ᴱ ++ᶜ D₀)) eρL xL)
            ≡ y₁
        eyL = split→∈-unique₂ eΓ₁L eΓ₂L eT sL (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})

        slL = sl-eq eρL eT xL y₁ eyL

        eUL : subst (_⊢V⦂ B) slL VL ≡ U₁
        eUL =
          trans (cong (subst (_⊢V⦂ B) slL)
                  (trans (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sL)))
                               (trans (restrict-castᵛ cWL et W)
                                      (castᵛ≡subst (cong _ᴱ cWL)
                                        (eternal-val-restrict et W))))
                         (subst-fuseᵛ (cong _ᴱ cWL)
                                      (sym (split→∈-split-l sL))
                                      (eternal-val-restrict et W))))
            (trans (subst-fuseᵛ (trans (cong _ᴱ cWL)
                                       (sym (split→∈-split-l sL)))
                                slL (eternal-val-restrict et W))
              (trans (substᵛ-irr (trans (trans (cong _ᴱ cWL)
                                               (sym (split→∈-split-l sL)))
                                        slL)
                        (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                        (eternal-val-restrict et W))
                     (sym (castᵛ≡subst
                             (sym (split→∈-split-l (split-≡-++ᶜ {Γ ᴱ ∷ B} {Θ₀})))
                             (eternal-val-restrict et W)))))

        subCL : H⁺ [ y₁ ↦ U₁ ]c
              ≡ subst (_⊢C⦂ CT)
                  (cong₂ _++ᶜ_ slL (sr-eq eρL eT xL y₁ eyL))
                  (Ĥ [ xL ↦ VL ]c)
        subCL = sub-cast-C″ eρL eT Ĥ xL y₁ eyL VL U₁ eUL

        inner-eq-L : subst (_⊢C⦂ CT) eLL
                       (castᶜ cDL (subst (_⊢C⦂ CT) bigEL (Ĥ [ xL ↦ VL ]c)))
                   ≡ castᶜ (castOf {Γ ᴱ} {B} Θ₀) (H⁺ [ y₁ ↦ U₁ ]c)
        inner-eq-L =
          trans (cong (subst (_⊢C⦂ CT) eLL)
                  (trans (castᶜ≡subst cDL _)
                         (subst-fuseᶜ bigEL cDL _)))
            (trans (subst-fuseᶜ (trans bigEL cDL) eLL _)
              (trans (cong (λ p → subst (_⊢C⦂ CT) p (Ĥ [ xL ↦ VL ]c))
                           (uip {p = trans (trans bigEL cDL) eLL}
                                {q = trans (cong₂ _++ᶜ_ slL
                                             (sr-eq eρL eT xL y₁ eyL))
                                           (castOf {Γ ᴱ} {B} Θ₀)}))
                (sym (trans (castᶜ≡subst (castOf {Γ ᴱ} {B} Θ₀) _)
                       (trans (cong (subst (_⊢C⦂ CT) (castOf {Γ ᴱ} {B} Θ₀))
                                    subCL)
                              (subst-fuseᶜ (cong₂ _++ᶜ_ slL
                                             (sr-eq eρL eT xL y₁ eyL))
                                           (castOf {Γ ᴱ} {B} Θ₀) _))))))

        -- the right substitution, likewise

        eΓ₁R = cong _ᴱ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
        eΓ₂R = cong (λ Γ₁ → Γ₁ ᴱ ++ᶜ D₀)
                    (sym (split→∈-split-r (split-≡-++ᶜ {Γ' ∷ B} {Θ})))

        eρR = cong ctx-grade eΓ₂R

        eyR : subst (λ Γ₀ → B ∈[ ctx-grade ((split-r z₀') ᴱ ++ᶜ D₀) ] Γ₀)
                    (sym eTΓ')
                (subst (λ ρ₀ → B ∈[ ρ₀ ] ((Γ' ᴱ ∷ B) ++ᶜ Θ₀)) eρR y₂)
            ≡ xR
        eyR = split→∈-unique₂ eΓ₁R eΓ₂R (sym eTΓ')
                              (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀}) sR

        slR = sl-eq eρR (sym eTΓ') y₂ xR eyR

        VR″ = subst (_⊢V⦂ B) slR U₂

        X₂ = (C-rename KR H⁺) [ y₂ ↦ U₂ ]c

        subCR : (subst (_⊢C⦂ CT) (sym eTΓ') (C-rename KR H⁺)) [ xR ↦ VR″ ]c
              ≡ subst (_⊢C⦂ CT)
                  (cong₂ _++ᶜ_ slR (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                  X₂
        subCR = sub-cast-C″ eρR (sym eTΓ') (C-rename KR H⁺) y₂ xR eyR
                            U₂ VR″ refl

        eVR : VR ≐ᵛ VR″
        eVR =
          ≐ᵛ-trans
            (≡→≐ᵛ (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sR)))
                        (restrict-castᵛ cWR et (V-rename r W))))
            (≐ᵛ-trans
              (substᵛ-≐ (sym (split→∈-split-l sR))
                 (castᵛ-≐ (cong _ᴱ cWR) (eternal-val-restrict-ren et r W)))
              (≡→≐ᵛ
                (trans (cong (subst (_⊢V⦂ B) (sym (split→∈-split-l sR)))
                             (castᵛ≡subst (cong _ᴱ cWR)
                               (V-rename (restrict-ren {Ξ = []} r)
                                         (eternal-val-restrict et W))))
                  (trans (subst-fuseᵛ (cong _ᴱ cWR)
                                      (sym (split→∈-split-l sR))
                                      (V-rename (restrict-ren {Ξ = []} r)
                                                (eternal-val-restrict et W)))
                    (trans (substᵛ-irr
                              (trans (cong _ᴱ cWR)
                                     (sym (split→∈-split-l sR)))
                              (trans (sym (split→∈-split-l
                                            (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                     slR)
                              (V-rename (restrict-ren {Ξ = []} r)
                                        (eternal-val-restrict et W)))
                      (sym (trans (cong (subst (_⊢V⦂ B) slR)
                                        (castᵛ≡subst
                                          (sym (split→∈-split-l
                                                 (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                          (V-rename (restrict-ren {Ξ = []} r)
                                                    (eternal-val-restrict et W))))
                                  (subst-fuseᵛ
                                    (sym (split→∈-split-l
                                           (split-≡-++ᶜ {Γ' ᴱ ∷ B} {Θ₀})))
                                    slR
                                    (V-rename (restrict-ren {Ξ = []} r)
                                              (eternal-val-restrict et W))))))))))

        TRfin = trans (trans (cong₂ _++ᶜ_ slR
                               (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                             bigER)
                      cDR

        gr-chain : castᶜ cDR
                     (subst (_⊢C⦂ CT) bigER
                       ((C-rename (cong-∷-ren (cong-∷-ren
                                    (restrict-ren {Ξ = []}
                                      (cong-ren {Γ'' = Θ} (cong-∷-ren r)))))
                                  Ĥ)
                          [ xR ↦ VR ]c))
                 ≐ᶜ subst (_⊢C⦂ CT) TRfin X₂
        gr-chain =
          ≐ᶜ-trans
            (castᶜ-≐ cDR (substᶜ-≐ bigER
              (sub-≐ᶜ xR eVR
                 (C-rename-conj eT (sym eTΓ')
                    (clause-ren-r-et-≐ r et Θ D₀) Ĥ))))
            (≐ᶜ-trans
              (≡→≐ᶜ (cong (λ z → castᶜ cDR (subst (_⊢C⦂ CT) bigER z)) subCR))
              (≡→≐ᶜ (trans (cong (castᶜ cDR)
                              (subst-fuseᶜ (cong₂ _++ᶜ_ slR
                                             (sr-eq eρR (sym eTΓ') y₂ xR eyR))
                                           bigER X₂))
                       (trans (castᶜ≡subst cDR _)
                              (subst-fuseᶜ (trans (cong₂ _++ᶜ_ slR
                                                    (sr-eq eρR (sym eTΓ')
                                                           y₂ xR eyR))
                                                  bigER)
                                           cDR X₂)))))

        out-eq : subst (_⊢C⦂ CT) eLL'
                   (castᶜ (castOf {Γ' ᴱ} {B} Θ₀) X₂)
               ≡ subst (_⊢C⦂ CT) TRfin X₂
        out-eq =
          trans (cong (subst (_⊢C⦂ CT) eLL')
                      (castᶜ≡subst (castOf {Γ' ᴱ} {B} Θ₀) X₂))
            (trans (subst-fuseᶜ (castOf {Γ' ᴱ} {B} Θ₀) eLL' X₂)
                   (cong (λ p → subst (_⊢C⦂ CT) p X₂)
                         (uip {p = trans (castOf {Γ' ᴱ} {B} Θ₀) eLL'}
                              {q = TRfin})))

-- The dispatcher: the two halves' own statements each fit the unreduced
-- goal, so a `Dec` argument is matched instead of a `with`.

ren-sub-handle : ∀ {Γ Γ' B A B' ε ε'} → (r : Ren [] Γ Γ') → (Θ : Ctx)
               → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
               → (H : (op : Op) → (ε'' : E) →
                        ((Γ ∷ B) ++ᶜ Θ) ᴱ ∷ type-of-gtype (param op)
                          ∷ [ mapᵉ (op-grade op) ]
                              (type-of-gtype (arity op) ⇒ B' ‼ ε'')
                        ⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
               → (N : ((Γ ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ B' ‼ ε')
               → (W : Γ ⊢V⦂ B)
               → (hM : RenSubC r Θ M W)
               → (hN : RenSubC r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
               → (hH : (et : Eternal B) → (op : Op) → (ε'' : E)
                     → RenSubC {Γ ᴱ} {Γ' ᴱ} {B}
                         (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                         (subst (_⊢C⦂ B' ‼ (op-grade op ·ₑ ε''))
                                (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                                (H op ε''))
                         (eternal-val-restrict et W))
               → RenSubC r Θ (handle M `with H `in N) W

ren-sub-handle {B = B} r Θ M H N W hM hN hH = go (eternal? B)
  where
    go : Dec (Eternal B) → _
    go (yes et) = ren-sub-handle-et r Θ et M H N W hM hN (hH et)
    go (no ¬et) = ren-sub-handle-ne r Θ ¬et M H N W hM hN

-- RENAMING THE PREFIX COMMUTES WITH SUBSTITUTING AT THE VARIABLE PAST IT
--
-- Mutual induction on the term, at an arbitrary suffix, as `sub-wk`: each
-- binding former grows the suffix, `cong-ren {Θ ∷ A} r` *is*
-- `cong-∷-ren (cong-ren {Θ} r)` and the substituted variable at `Θ ∷ A` *is*
-- `Tl-∷` of the one at `Θ`, both definitionally. What is left per case is
-- pushing the two casts through the former.

mutual

  ren-sub-V : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {A}
            → (U : ((Γ ∷ B) ++ᶜ Θ) ⊢V⦂ A) → (W : Γ ⊢V⦂ B)
            → V-rename (cong-ren {Γ'' = Θ} r)
                (castᵛ (castOf {Γ} {B} Θ)
                  (U [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]v))
            ≐ᵛ castᵛ (castOf {Γ'} {B} Θ)
                 ((V-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) U)
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]v)

  ren-sub-V {Γ} {Γ'} {B} r Θ (var f y) W = ren-sub-var r Θ y W f f

  ren-sub-V {Γ} {Γ'} {B} r Θ (const c) W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-const (castOf {Γ} {B} Θ))))
             (≡→≐ᵛ (sym (cast-const (castOf {Γ'} {B} Θ))))

  ren-sub-V {Γ} {Γ'} {B} r Θ ⋆ W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-⋆ (castOf {Γ} {B} Θ))))
             (≡→≐ᵛ (sym (cast-⋆ (castOf {Γ'} {B} Θ))))

  ren-sub-V {Γ} {Γ'} {B} r Θ ⦉ V₁ , V₂ ⦊ W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-pair (castOf {Γ} {B} Θ))))
      (≐ᵛ-trans (pair-≐ (ren-sub-V r Θ V₁ W) (ren-sub-V r Θ V₂ W))
                (≡→≐ᵛ (sym (cast-pair (castOf {Γ'} {B} Θ)))))

  ren-sub-V {Γ} {Γ'} {B} r Θ {A = A ⇒ C} (lam M) W =
    ≐ᵛ-trans (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ} r))
                         (cast-lam (castOf {Γ} {B} Θ) _)))
      (≐ᵛ-trans
        (lam-≐ (≐ᶜ-trans
                 (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A} r))
                             (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ A)) _)))
                 (≐ᶜ-trans (ren-sub-C r (Θ ∷ A) M W)
                           (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A))
                                            (cong (_∷ A) (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᵛ (sym (cast-lam (castOf {Γ'} {B} Θ) _))))

  ren-sub-C : ∀ {Γ Γ' B} → (r : Ren [] Γ Γ') → (Θ : Ctx) → ∀ {C}
            → (M : ((Γ ∷ B) ++ᶜ Θ) ⊢C⦂ C) → (W : Γ ⊢V⦂ B)
            → C-rename (cong-ren {Γ'' = Θ} r)
                (castᶜ (castOf {Γ} {B} Θ)
                  (M [ split→∈ (split-≡-++ᶜ {Γ ∷ B} {Θ})
                       ↦ castᵛ (sym (split→∈-split-l
                                       (split-≡-++ᶜ {Γ ∷ B} {Θ}))) W ]c))
            ≐ᶜ castᶜ (castOf {Γ'} {B} Θ)
                 ((C-rename (cong-ren {Γ'' = Θ} (cong-∷-ren r)) M)
                    [ split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})
                      ↦ castᵛ (sym (split→∈-split-l
                                      (split-≡-++ᶜ {Γ' ∷ B} {Θ})))
                              (V-rename r W) ]c)

  ren-sub-C {Γ} {Γ'} {B} r Θ (return V) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-ret (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (return-≐ (ren-sub-V r Θ V W))
                (≡→≐ᶜ (sym (cast-ret (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (_⨟_ {A = A} {ε = ε} M N) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-seq (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (seq-≐ (ren-sub-C r Θ M W)
               (≐ᶜ-trans
                 (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ mapᵉ ε ⟩ ∷ A} r))
                             (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                              (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))
                 (≐ᶜ-trans (ren-sub-C r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
                           (≡→≐ᶜ (castᶜ-irr
                                    (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A))
                                    (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A)
                                          (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-seq (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (V₁ · V₂) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-app (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (app-≐ (ren-sub-V r Θ V₁ W) (ren-sub-V r Θ V₂ W))
                (≡→≐ᶜ (sym (cast-app (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (match_`in_ {A = A} {B = B'} V N) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-match (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (match-≐ (ren-sub-V r Θ V W)
                 (≐ᶜ-trans
                   (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ A ∷ B'} r))
                               (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A ∷ B')
                                                (castOf {Γ} {B} Θ))
                                          (castOf {Γ} {B} (Θ ∷ A ∷ B')) _)))
                   (≐ᶜ-trans (ren-sub-C r (Θ ∷ A ∷ B') N W)
                             (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ A ∷ B'))
                                              (cong (λ Γ₀ → Γ₀ ∷ A ∷ B')
                                                    (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-match (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (absurd V) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-absurd (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (absurd-≐ (ren-sub-V r Θ V W))
                (≡→≐ᶜ (sym (cast-absurd (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (perform op V M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-perform (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (perform-≐ (ren-sub-V r Θ V W)
                   (≐ᶜ-trans
                     (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ'} r))
                                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                            ∷ type-of-gtype (arity op))
                                                  (castOf {Γ} {B} Θ))
                                            (castOf {Γ} {B} Θ') _)))
                     (≐ᶜ-trans (ren-sub-C r Θ' M W)
                               (≡→≐ᶜ (castᶜ-irr
                                        (castOf {Γ'} {B} Θ')
                                        (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                                        ∷ type-of-gtype (arity op))
                                              (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-perform (castOf {Γ'} {B} Θ)))))
    where
      Θ' = Θ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)

  ren-sub-C {Γ} {Γ'} {B} r Θ (delay τ M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-delay (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (delay-≐ (≐ᶜ-trans
                   (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ⟨ of-natʳ τ ⟩} r))
                               (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ} {B} Θ))
                                          (castOf {Γ} {B} (Θ ⟨ of-natʳ τ ⟩)) _)))
                   (≐ᶜ-trans (ren-sub-C r (Θ ⟨ of-natʳ τ ⟩) M W)
                             (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ⟨ of-natʳ τ ⟩))
                                              (cong (_⟨ of-natʳ τ ⟩)
                                                    (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-delay (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (box {A = A} {ρ = ρ} V M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-box (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans
        (box-≐ (≐ᵛ-trans
                 (≡→≐ᵛ (cong (V-rename (cong-ren {Γ'' = Θ ⟨ ρ ⟩} r))
                             (castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ⟨ ρ ⟩)) _)))
                 (≐ᵛ-trans (ren-sub-V r (Θ ⟨ ρ ⟩) V W)
                           (≡→≐ᵛ (castᵛ-irr (castOf {Γ'} {B} (Θ ⟨ ρ ⟩))
                                            (cong (_⟨ ρ ⟩) (castOf {Γ'} {B} Θ)) _))))
               (≐ᶜ-trans
                 (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ ∷ [ ρ ] A} r))
                             (castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ} {B} Θ))
                                        (castOf {Γ} {B} (Θ ∷ [ ρ ] A)) _)))
                 (≐ᶜ-trans (ren-sub-C r (Θ ∷ [ ρ ] A) M W)
                           (≡→≐ᶜ (castᶜ-irr (castOf {Γ'} {B} (Θ ∷ [ ρ ] A))
                                            (cong (_∷ [ ρ ] A)
                                                  (castOf {Γ'} {B} Θ)) _)))))
        (≡→≐ᶜ (sym (cast-box (castOf {Γ'} {B} Θ)))))

  ren-sub-C {Γ} {Γ'} {B} r Θ (coerce p M) W =
    ≐ᶜ-trans (≡→≐ᶜ (cong (C-rename (cong-ren {Γ'' = Θ} r))
                         (cast-coerce (castOf {Γ} {B} Θ))))
      (≐ᶜ-trans (coerce-≐ (ren-sub-C r Θ M W))
                (≡→≐ᶜ (sym (cast-coerce (castOf {Γ'} {B} Θ)))))

  -- the clause hypothesis is the recursion at the canonical restricted
  -- contexts, threaded through `ren-sub-C-cast` so it runs on the bare clause
  ren-sub-C {Γ} {Γ'} {B} r Θ (handle_`with_`in {A = A} {B = B'} {ε = ε} M H N) W =
    ren-sub-handle r Θ M H N W
      (ren-sub-C r Θ M W)
      (ren-sub-C r (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
      (λ et op ε'' →
         ren-sub-C-cast (restrict-ren {Ξ = []} r) (Θ ᴱ ++ᶜ Dcl B' op ε'')
                        (ren-sub-eTot {Γ} {B} Θ et (Dcl B' op ε''))
                        (H op ε'') (eternal-val-restrict et W))
  ren-sub-C r Θ (unbox {A = A} w V M)    W =
    ren-sub-unbox r Θ w V M W (ren-sub-C r (Θ ∷ A) M W)

  -- `ren-sub-C` with its context given by an equation, so the `handle` clause
  -- can recurse on the bare clause term (as `sub-wk-C-cast`).

  ren-sub-C-cast : ∀ {Γ Γ' B Γ₀} → (r : Ren [] Γ Γ') → (Θ : Ctx)
                 → ∀ {C} → (e : Γ₀ ≡ (Γ ∷ B) ++ᶜ Θ) → (M : Γ₀ ⊢C⦂ C)
                 → (W : Γ ⊢V⦂ B)
                 → RenSubC r Θ (subst (_⊢C⦂ C) e M) W

  ren-sub-C-cast r Θ refl M W = ren-sub-C r Θ M W

------------------------------------------------------------------------
-- SUB-SWAP: TWO ADJACENT PREFIX SUBSTITUTIONS COMMUTE
--
-- Replacing the outer entry (its value weakened past the inner one) and
-- then the inner one agrees with replacing the inner entry, the outer one
-- riding in the suffix, and then the outer one.
--
-- The right-hand order names the *inner* entry `B₁` with the outer one
-- riding in the suffix. Rather than a `split-++ʳ` splitting, that is
-- presented as the ordinary `split-≡-++ᶜ` at the suffix `([] ∷ B₂) ++ᶜ Θ`
-- applied to an associativity-cast term — the two are interchangeable
-- (`sub-cast-C`), and this way `sub-var-r`/`-l`/`-hit` apply verbatim,
-- since `B₂` and `Θ`'s variables are then literally variables of that
-- suffix. The cast pushes through every former for free: the proof
-- `++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) (Θ ∷ A)` *is*
-- `cong (_∷ A) (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ)`, definitionally.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- SUBSTITUTING AT THE PREFIX BOUNDARY
--
-- The whole development is phrased in this one abbreviation: replace the
-- entry sitting between `Γ'` and the suffix `Θ` by a value over `Γ'`,
-- presenting the result over `Γ' ++ᶜ Θ`.
------------------------------------------------------------------------

bvar : ∀ {Γ'} → (B : VType) → (Θ : Ctx) → B ∈[ ctx-grade Θ ] ((Γ' ∷ B) ++ᶜ Θ)
bvar {Γ'} B Θ = split→∈ (split-≡-++ᶜ {Γ' ∷ B} {Θ})

bval : ∀ {Γ' B} → (Θ : Ctx) → Γ' ⊢V⦂ B
     → split-l (bvar {Γ'} B Θ) ⊢V⦂ B
bval {Γ'} {B} Θ W =
  castᵛ (sym (split→∈-split-l (split-≡-++ᶜ {Γ' ∷ B} {Θ}))) W

sub-atᵛ : ∀ {Γ' B A} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢V⦂ A
sub-atᵛ {Γ'} {B} Θ U W =
  castᵛ (castOf {Γ'} {B} Θ) (U [ bvar B Θ ↦ bval Θ W ]v)

sub-atᶜ : ∀ {Γ' B C} → (Θ : Ctx) → ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C → Γ' ⊢V⦂ B
        → (Γ' ++ᶜ Θ) ⊢C⦂ C
sub-atᶜ {Γ'} {B} Θ M W =
  castᶜ (castOf {Γ'} {B} Θ) (M [ bvar B Θ ↦ bval Θ W ]c)

-- and on a clause family, where the substitution reaches through
-- `⟨_⟩[_↦_]cl` and the transport is `Cl-cast`, i.e. exactly the shape
-- `cast-handle` produces

sub-atᴴ : ∀ {Γ' B D} → (Θ : Ctx) → Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ) → Γ' ⊢V⦂ B
        → Fam D ((Γ' ++ᶜ Θ) ᴱ)
sub-atᴴ {Γ'} {B} Θ H W op ε =
  Cl-cast op ε (castOf {Γ'} {B} Θ)
    (⟨ eternal? B ⟩[ bvar B Θ ↦ bval Θ W ]cl H op ε)

------------------------------------------------------------------------
-- THE FORMER LAWS
--
-- One per constructor: the action commutes with it, the suffix growing by
-- the former's own binders. Each is the corresponding `cast-*` lemma, plus
-- `castᶜ-irr`/`castᵛ-irr` wherever a binder makes the two ways of naming
-- the context equality differ (only propositionally).
------------------------------------------------------------------------

sub-at-const : ∀ {Γ' B b} → (Θ : Ctx) → {c : BaseConstants b} → (W : Γ' ⊢V⦂ B)
             → sub-atᵛ Θ (const c) W ≡ const c
sub-at-const {Γ'} {B} Θ W = cast-const (castOf {Γ'} {B} Θ)

sub-at-⋆ : ∀ {Γ' B} → (Θ : Ctx) → (W : Γ' ⊢V⦂ B) → sub-atᵛ Θ ⋆ W ≡ ⋆
sub-at-⋆ {Γ'} {B} Θ W = cast-⋆ (castOf {Γ'} {B} Θ)

sub-at-pair : ∀ {Γ' B A₁ A₂} → (Θ : Ctx)
            → (V₁ : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A₁) → (V₂ : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A₂)
            → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ ⦉ V₁ , V₂ ⦊ W ≡ ⦉ sub-atᵛ Θ V₁ W , sub-atᵛ Θ V₂ W ⦊
sub-at-pair {Γ'} {B} Θ V₁ V₂ W = cast-pair (castOf {Γ'} {B} Θ)

sub-at-lam : ∀ {Γ' B A C} → (Θ : Ctx)
           → (N : ((Γ' ∷ B) ++ᶜ Θ) ∷ A ⊢C⦂ C) → (W : Γ' ⊢V⦂ B)
           → sub-atᵛ Θ (lam N) W ≡ lam (sub-atᶜ (Θ ∷ A) N W)
sub-at-lam {Γ'} {B} {A} Θ N W =
  trans (cast-lam (castOf {Γ'} {B} Θ) _)
        (cong lam (castᶜ-irr (cong (_∷ A) (castOf {Γ'} {B} Θ))
                             (castOf {Γ'} {B} (Θ ∷ A)) _))

sub-at-ret : ∀ {Γ' B A} → (Θ : Ctx) → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A)
           → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (return V) W ≡ return (sub-atᵛ Θ V W)
sub-at-ret {Γ'} {B} Θ V W = cast-ret (castOf {Γ'} {B} Θ)

sub-at-app : ∀ {Γ' B A C} → (Θ : Ctx)
           → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A ⇒ C) → (U : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A)
           → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (V · U) W ≡ (sub-atᵛ Θ V W · sub-atᵛ Θ U W)
sub-at-app {Γ'} {B} Θ V U W = cast-app (castOf {Γ'} {B} Θ)

sub-at-absurd : ∀ {Γ' B C} → (Θ : Ctx) → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ Empty)
              → (W : Γ' ⊢V⦂ B)
              → sub-atᶜ {C = C} Θ (absurd V) W ≡ absurd (sub-atᵛ Θ V W)
sub-at-absurd {Γ'} {B} Θ V W = cast-absurd (castOf {Γ'} {B} Θ)

sub-at-coerce : ∀ {Γ' B A ε ε'} → (Θ : Ctx) → {p : ε ≾ₑ ε'}
              → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε) → (W : Γ' ⊢V⦂ B)
              → sub-atᶜ Θ (coerce p M) W ≡ coerce p (sub-atᶜ Θ M W)
sub-at-coerce {Γ'} {B} Θ M W = cast-coerce (castOf {Γ'} {B} Θ)

sub-at-seq : ∀ {Γ' B A A' ε ε'} → (Θ : Ctx)
           → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
           → (N : ((Γ' ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ A' ‼ ε')
           → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (M ⨟ N) W
           ≡ (sub-atᶜ Θ M W ⨟ sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
sub-at-seq {Γ'} {B} {A} {ε = ε} Θ M N W =
  trans (cast-seq (castOf {Γ'} {B} Θ))
        (cong (_ ⨟_)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))

sub-at-match : ∀ {Γ' B A₁ A₂ C} → (Θ : Ctx)
             → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A₁ |×| A₂)
             → (N : ((Γ' ∷ B) ++ᶜ Θ) ∷ A₁ ∷ A₂ ⊢C⦂ C) → (W : Γ' ⊢V⦂ B)
             → sub-atᶜ Θ (match V `in N) W
             ≡ match sub-atᵛ Θ V W `in (sub-atᶜ (Θ ∷ A₁ ∷ A₂) N W)
sub-at-match {Γ'} {B} {A₁} {A₂} Θ V N W =
  trans (cast-match (castOf {Γ'} {B} Θ))
        (cong (match _ `in_)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A₁ ∷ A₂) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ∷ A₁ ∷ A₂)) _))

sub-at-perform : ∀ {Γ' B A ε} → (Θ : Ctx) → {op : Op}
               → (V : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ type-of-gtype (param op))
               → (N : ((Γ' ∷ B) ++ᶜ Θ) ⟨ mapᵉ (op-grade op) ⟩
                        ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
               → (W : Γ' ⊢V⦂ B)
               → sub-atᶜ Θ (perform op V N) W
               ≡ perform op (sub-atᵛ Θ V W)
                   (sub-atᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                               ∷ type-of-gtype (arity op)) N W)
sub-at-perform {Γ'} {B} Θ {op = op} V N W =
  trans (cast-perform (castOf {Γ'} {B} Θ))
        (cong (perform op _)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                          ∷ type-of-gtype (arity op))
                               (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))) _))

sub-at-delay : ∀ {Γ' B A ε τ} → (Θ : Ctx)
             → (M : ((Γ' ∷ B) ++ᶜ Θ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε) → (W : Γ' ⊢V⦂ B)
             → sub-atᶜ Θ (delay τ M) W ≡ delay τ (sub-atᶜ (Θ ⟨ of-natʳ τ ⟩) M W)
sub-at-delay {Γ'} {B} {τ = τ} Θ M W =
  trans (cast-delay (castOf {Γ'} {B} Θ))
        (cong (delay τ)
              (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ of-natʳ τ ⟩)) _))

sub-at-box : ∀ {Γ' B A C ρ} → (Θ : Ctx)
           → (V : ((Γ' ∷ B) ++ᶜ Θ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : ((Γ' ∷ B) ++ᶜ Θ) ∷ [ ρ ] A ⊢C⦂ C) → (W : Γ' ⊢V⦂ B)
           → sub-atᶜ Θ (box V M) W
           ≡ box (sub-atᵛ (Θ ⟨ ρ ⟩) V W) (sub-atᶜ (Θ ∷ [ ρ ] A) M W)
sub-at-box {Γ'} {B} {A} {ρ = ρ} Θ V M W =
  trans (cast-box (castOf {Γ'} {B} Θ))
        (cong₂ box
          (castᵛ-irr (cong (_⟨ ρ ⟩) (castOf {Γ'} {B} Θ))
                     (castOf {Γ'} {B} (Θ ⟨ ρ ⟩)) _)
          (castᶜ-irr (cong (_∷ [ ρ ] A) (castOf {Γ'} {B} Θ))
                     (castOf {Γ'} {B} (Θ ∷ [ ρ ] A)) _))

sub-at-handle : ∀ {Γ' B A D ε ε'} → (Θ : Ctx)
              → (M : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
              → (H : Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ))
              → (N : ((Γ' ∷ B) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
              → (W : Γ' ⊢V⦂ B)
              → sub-atᶜ Θ (handle M `with H `in N) W
              ≡ handle (sub-atᶜ Θ M W)
                 `with sub-atᴴ Θ H W
                 `in (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W)
sub-at-handle {Γ'} {B} {A} {ε = ε} Θ M H N W =
  trans (cast-handle (castOf {Γ'} {B} Θ))
        (cong (λ z → handle _ `with _ `in z)
              (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (castOf {Γ'} {B} Θ))
                         (castOf {Γ'} {B} (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))

------------------------------------------------------------------------
-- THE TWO ORDERS
--
-- `outer-first` replaces `B₂` (its value weakened past `B₁`) and then
-- `B₁`; `inner-first` replaces `B₁`, with `B₂` riding in the suffix, and
-- then `B₂`. The associativity is what re-brackets `B₂` into the suffix;
-- at a grown suffix it is `cong` of itself, definitionally, so it costs
-- nothing at the non-binding formers and one `castᶜ-irr` at the binding
-- ones.
------------------------------------------------------------------------

assocᴮ : (Γ : Ctx) → (B₁ B₂ : VType) → (Θ : Ctx)
       → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ≡ ((Γ ∷ B₁) ++ᶜ (([] ∷ B₂) ++ᶜ Θ))
assocᴮ Γ B₁ B₂ Θ = ++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ

assocᴮ⁻ : (Γ : Ctx) → (B₂ : VType) → (Θ : Ctx)
        → (Γ ++ᶜ (([] ∷ B₂) ++ᶜ Θ)) ≡ ((Γ ∷ B₂) ++ᶜ Θ)
assocᴮ⁻ Γ B₂ Θ = sym (++ᶜ-assoc Γ ([] ∷ B₂) Θ)

outerᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢V⦂ A
outerᵛ {B₁ = B₁} Θ U W₂ W₁ =
  sub-atᵛ Θ (sub-atᵛ Θ U (V-rename (wk-ren {A = B₁}) W₂)) W₁

outerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
outerᶜ {B₁ = B₁} Θ M W₂ W₁ =
  sub-atᶜ Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)) W₁

-- `B₁` alone, with `B₂` re-bracketed into the suffix. Both orders' second
-- step is then an ordinary `sub-atᵛ`/`sub-atᶜ`, so only this operation
-- needs former laws of its own.

inner₀ᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
        → Γ ⊢V⦂ B₁ → ((Γ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
inner₀ᵛ {Γ} {B₁} {B₂} Θ U W₁ =
  castᵛ (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) (castᵛ (assocᴮ Γ B₁ B₂ Θ) U) W₁)

inner₀ᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
        → Γ ⊢V⦂ B₁ → ((Γ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
inner₀ᶜ {Γ} {B₁} {B₂} Θ M W₁ =
  castᶜ (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) (castᶜ (assocᴮ Γ B₁ B₂ Θ) M) W₁)

inner₀ᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
        → Γ ⊢V⦂ B₁ → Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
inner₀ᴴ {Γ} {B₁} {B₂} Θ H W₁ op ε =
  Cl-cast op ε (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᴴ (([] ∷ B₂) ++ᶜ Θ)
       (λ op' ε' → Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')) W₁ op ε)

innerᵛ : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢V⦂ A
innerᵛ Θ U W₂ W₁ = sub-atᵛ Θ (inner₀ᵛ Θ U W₁) W₂

innerᶜ : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → (Γ ++ᶜ Θ) ⊢C⦂ C
innerᶜ Θ M W₂ W₁ = sub-atᶜ Θ (inner₀ᶜ Θ M W₁) W₂

-- and on a clause family

outerᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Fam D ((Γ ++ᶜ Θ) ᴱ)
outerᴴ {B₁ = B₁} Θ H W₂ W₁ =
  sub-atᴴ Θ (sub-atᴴ Θ H (V-rename (wk-ren {A = B₁}) W₂)) W₁

innerᴴ : ∀ {Γ B₁ B₂ D} → (Θ : Ctx) → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ)
       → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Fam D ((Γ ++ᶜ Θ) ᴱ)
innerᴴ Θ H W₂ W₁ = sub-atᴴ Θ (inner₀ᴴ Θ H W₁) W₂

------------------------------------------------------------------------
-- `inner₀`'S FORMER LAWS
--
-- Each is `cast-F` (pushing the associativity in), `sub-at-F`, `cast-F`
-- again (pushing the inverse out); the binding formers add one
-- `castᶜ-irr`, since `cong (_∷ A) (sym p)` and `sym (cong (_∷ A) p)`
-- agree only propositionally. Note the associativity itself needs no
-- reconciliation: `++ᶜ-assoc Γ' Δ (Θ ∷ A)` *is* `cong (_∷ A)` of the one
-- at `Θ`, definitionally.
------------------------------------------------------------------------

inner₀-const : ∀ {Γ B₁ B₂ b} → (Θ : Ctx) → {c : BaseConstants b}
             → (W₁ : Γ ⊢V⦂ B₁)
             → inner₀ᵛ {B₂ = B₂} Θ (const c) W₁ ≡ const c
inner₀-const {Γ} {B₁} {B₂} Θ W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-const (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-const (([] ∷ B₂) ++ᶜ Θ) W₁)))
        (cast-const (assocᴮ⁻ Γ B₂ Θ))

inner₀-⋆ : ∀ {Γ B₁ B₂} → (Θ : Ctx) → (W₁ : Γ ⊢V⦂ B₁)
         → inner₀ᵛ {B₂ = B₂} Θ ⋆ W₁ ≡ ⋆
inner₀-⋆ {Γ} {B₁} {B₂} Θ W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-⋆ (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-⋆ (([] ∷ B₂) ++ᶜ Θ) W₁)))
        (cast-⋆ (assocᴮ⁻ Γ B₂ Θ))

inner₀-pair : ∀ {Γ B₁ B₂ A₁ A₂} → (Θ : Ctx)
            → (V₁ : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A₁)
            → (V₂ : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A₂) → (W₁ : Γ ⊢V⦂ B₁)
            → inner₀ᵛ Θ ⦉ V₁ , V₂ ⦊ W₁
            ≡ ⦉ inner₀ᵛ Θ V₁ W₁ , inner₀ᵛ Θ V₂ W₁ ⦊
inner₀-pair {Γ} {B₁} {B₂} Θ V₁ V₂ W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-pair (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-pair (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V₁)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V₂) W₁)))
        (cast-pair (assocᴮ⁻ Γ B₂ Θ))

inner₀-lam : ∀ {Γ B₁ B₂ A C} → (Θ : Ctx)
           → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A ⊢C⦂ C) → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᵛ {B₂ = B₂} Θ (lam N) W₁ ≡ lam (inner₀ᶜ (Θ ∷ A) N W₁)
inner₀-lam {Γ} {B₁} {B₂} {A} Θ N W₁ =
  trans (cong (castᵛ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᵛ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-lam (assocᴮ Γ B₁ B₂ Θ) N))
                 (sub-at-lam (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ∷ A)) N) W₁)))
    (trans (cast-lam (assocᴮ⁻ Γ B₂ Θ) _)
           (cong lam (castᶜ-irr (cong (_∷ A) (assocᴮ⁻ Γ B₂ Θ))
                                (assocᴮ⁻ Γ B₂ (Θ ∷ A)) _)))

inner₀-ret : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A)
           → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (return V) W₁ ≡ return (inner₀ᵛ Θ V W₁)
inner₀-ret {Γ} {B₁} {B₂} Θ V W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-ret (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-ret (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V) W₁)))
        (cast-ret (assocᴮ⁻ Γ B₂ Θ))

inner₀-app : ∀ {Γ B₁ B₂ A C} → (Θ : Ctx)
           → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A ⇒ C)
           → (U : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A) → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (V · U) W₁
           ≡ (inner₀ᵛ Θ V W₁ · inner₀ᵛ Θ U W₁)
inner₀-app {Γ} {B₁} {B₂} Θ V U W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-app (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-app (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) U) W₁)))
        (cast-app (assocᴮ⁻ Γ B₂ Θ))

inner₀-absurd : ∀ {Γ B₁ B₂ C} → (Θ : Ctx)
              → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ Empty) → (W₁ : Γ ⊢V⦂ B₁)
              → inner₀ᶜ {B₂ = B₂} {C = C} Θ (absurd V) W₁
              ≡ absurd (inner₀ᵛ Θ V W₁)
inner₀-absurd {Γ} {B₁} {B₂} Θ V W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-absurd (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-absurd (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V) W₁)))
        (cast-absurd (assocᴮ⁻ Γ B₂ Θ))

inner₀-coerce : ∀ {Γ B₁ B₂ A ε ε'} → (Θ : Ctx) → {p : ε ≾ₑ ε'}
              → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε) → (W₁ : Γ ⊢V⦂ B₁)
              → inner₀ᶜ {B₂ = B₂} Θ (coerce p M) W₁
              ≡ coerce p (inner₀ᶜ Θ M W₁)
inner₀-coerce {Γ} {B₁} {B₂} Θ M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-coerce (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-coerce (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ Θ) M) W₁)))
        (cast-coerce (assocᴮ⁻ Γ B₂ Θ))

inner₀-seq : ∀ {Γ B₁ B₂ A A' ε ε'} → (Θ : Ctx)
           → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
           → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ A' ‼ ε')
           → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (M ⨟ N) W₁
           ≡ (inner₀ᶜ Θ M W₁ ⨟ inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
inner₀-seq {Γ} {B₁} {B₂} {A} {ε = ε} Θ M N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-seq (assocᴮ Γ B₁ B₂ Θ))
                     (cong (castᶜ (assocᴮ Γ B₁ B₂ Θ) M ⨟_)
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))))
                 (sub-at-seq (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ Θ) M)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) N) W₁)))
    (trans (cast-seq (assocᴮ⁻ Γ B₂ Θ))
           (cong (_ ⨟_)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))

inner₀-match : ∀ {Γ B₁ B₂ A₁ A₂ C} → (Θ : Ctx)
             → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A₁ |×| A₂)
             → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A₁ ∷ A₂ ⊢C⦂ C) → (W₁ : Γ ⊢V⦂ B₁)
             → inner₀ᶜ {B₂ = B₂} Θ (match V `in N) W₁
             ≡ match inner₀ᵛ Θ V W₁ `in (inner₀ᶜ (Θ ∷ A₁ ∷ A₂) N W₁)
inner₀-match {Γ} {B₁} {B₂} {A₁} {A₂} Θ V N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-match (assocᴮ Γ B₁ B₂ Θ))
                     (cong (match castᵛ (assocᴮ Γ B₁ B₂ Θ) V `in_)
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ∷ A₁ ∷ A₂) (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ∷ A₁ ∷ A₂)) _))))
                 (sub-at-match (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ∷ A₁ ∷ A₂)) N) W₁)))
    (trans (cast-match (assocᴮ⁻ Γ B₂ Θ))
           (cong (match _ `in_)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ∷ A₁ ∷ A₂) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ∷ A₁ ∷ A₂)) _)))

inner₀-perform : ∀ {Γ B₁ B₂ A ε} → (Θ : Ctx) → {op : Op}
               → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ type-of-gtype (param op))
               → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ (op-grade op) ⟩
                        ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε)
               → (W₁ : Γ ⊢V⦂ B₁)
               → inner₀ᶜ {B₂ = B₂} Θ (perform op V N) W₁
               ≡ perform op (inner₀ᵛ Θ V W₁)
                   (inner₀ᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                               ∷ type-of-gtype (arity op)) N W₁)
inner₀-perform {Γ} {B₁} {B₂} Θ {op = op} V N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-perform (assocᴮ Γ B₁ B₂ Θ))
                     (cong (perform op (castᵛ (assocᴮ Γ B₁ B₂ Θ) V))
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                           ∷ type-of-gtype (arity op))
                                (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))) _))))
                 (sub-at-perform (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ Θ) V)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                              ∷ type-of-gtype (arity op))) N)
                    W₁)))
    (trans (cast-perform (assocᴮ⁻ Γ B₂ Θ))
           (cong (perform op _)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))
                                  (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                             ∷ type-of-gtype (arity op))) _)))

inner₀-delay : ∀ {Γ B₁ B₂ A ε τ} → (Θ : Ctx)
             → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ of-natʳ τ ⟩ ⊢C⦂ A ‼ ε)
             → (W₁ : Γ ⊢V⦂ B₁)
             → inner₀ᶜ {B₂ = B₂} Θ (delay τ M) W₁
             ≡ delay τ (inner₀ᶜ (Θ ⟨ of-natʳ τ ⟩) M W₁)
inner₀-delay {Γ} {B₁} {B₂} {τ = τ} Θ M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-delay (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-delay (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ of-natʳ τ ⟩)) M) W₁)))
    (trans (cast-delay (assocᴮ⁻ Γ B₂ Θ))
           (cong (delay τ)
                 (castᶜ-irr (cong (_⟨ of-natʳ τ ⟩) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ of-natʳ τ ⟩)) _)))

inner₀-box : ∀ {Γ B₁ B₂ A C ρ} → (Θ : Ctx)
           → (V : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ ρ ⟩ ⊢V⦂ A)
           → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ [ ρ ] A ⊢C⦂ C) → (W₁ : Γ ⊢V⦂ B₁)
           → inner₀ᶜ {B₂ = B₂} Θ (box V M) W₁
           ≡ box (inner₀ᵛ (Θ ⟨ ρ ⟩) V W₁) (inner₀ᶜ (Θ ∷ [ ρ ] A) M W₁)
inner₀-box {Γ} {B₁} {B₂} {A} {ρ = ρ} Θ V M W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                       (cast-box (assocᴮ Γ B₁ B₂ Θ)))
                 (sub-at-box (([] ∷ B₂) ++ᶜ Θ)
                    (castᵛ (assocᴮ Γ B₁ B₂ (Θ ⟨ ρ ⟩)) V)
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ∷ [ ρ ] A)) M) W₁)))
    (trans (cast-box (assocᴮ⁻ Γ B₂ Θ))
           (cong₂ box
             (castᵛ-irr (cong (_⟨ ρ ⟩) (assocᴮ⁻ Γ B₂ Θ))
                        (assocᴮ⁻ Γ B₂ (Θ ⟨ ρ ⟩)) _)
             (castᶜ-irr (cong (_∷ [ ρ ] A) (assocᴮ⁻ Γ B₂ Θ))
                        (assocᴮ⁻ Γ B₂ (Θ ∷ [ ρ ] A)) _)))

inner₀-handle : ∀ {Γ B₁ B₂ A D ε ε'} → (Θ : Ctx)
              → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
              → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
              → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
              → (W₁ : Γ ⊢V⦂ B₁)
              → inner₀ᶜ {B₂ = B₂} Θ (handle M `with H `in N) W₁
              ≡ handle (inner₀ᶜ Θ M W₁)
                 `with inner₀ᴴ Θ H W₁
                 `in (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
inner₀-handle {Γ} {B₁} {B₂} {A} {ε = ε} Θ M H N W₁ =
  trans (cong (castᶜ (assocᴮ⁻ Γ B₂ Θ))
          (trans (cong (λ z → sub-atᶜ (([] ∷ B₂) ++ᶜ Θ) z W₁)
                   (trans (cast-handle (assocᴮ Γ B₁ B₂ Θ))
                     (cong (λ z → handle castᶜ (assocᴮ Γ B₁ B₂ Θ) M
                                   `with (λ op' ε' →
                                            Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ)
                                              (H op' ε'))
                                   `in z)
                       (castᶜ-irr
                          (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ Γ B₁ B₂ Θ))
                          (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _))))
                 (sub-at-handle (([] ∷ B₂) ++ᶜ Θ)
                    (castᶜ (assocᴮ Γ B₁ B₂ Θ) M)
                    (λ op' ε' → Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε'))
                    (castᶜ (assocᴮ Γ B₁ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) N) W₁)))
    (trans (cast-handle (assocᴮ⁻ Γ B₂ Θ))
           (cong (λ z → handle _ `with _ `in z)
                 (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ mapᵉ ε ⟩ ∷ A) (assocᴮ⁻ Γ B₂ Θ))
                            (assocᴮ⁻ Γ B₂ (Θ ⟨ mapᵉ ε ⟩ ∷ A)) _)))

------------------------------------------------------------------------
-- THE STATEMENT
------------------------------------------------------------------------

SubSwapV : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapV Θ U W₂ W₁ = outerᵛ Θ U W₂ W₁ ≐ᵛ innerᵛ Θ U W₂ W₁

SubSwapC : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C
         → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁ → Set
SubSwapC Θ M W₂ W₁ = outerᶜ Θ M W₂ W₁ ≐ᶜ innerᶜ Θ M W₂ W₁

------------------------------------------------------------------------
-- THE SWAP
--
-- Mutual induction on the term at an arbitrary suffix, as `sub-wk` and
-- `ren-sub`. Each structural case is: unfold both orders by their former
-- laws, apply the congruence to the induction hypotheses at the grown
-- suffix, fold back.
------------------------------------------------------------------------

-- The action respects the equivalence: each zone is a substitution, and
-- substitution is a congruence.

-- Reading a transport equation in the other direction.

subst-flip : ∀ {a p} {X : Set a} {P : X → Set p} {u v : X}
           → (e : u ≡ v) → (m : P u) → (n : P v)
           → subst P e m ≡ n → subst P (sym e) n ≡ m
subst-flip refl m n q = sym q

sub-atᵛ-≐ : ∀ {Γ' B A} → (Θ : Ctx) → {U U' : ((Γ' ∷ B) ++ᶜ Θ) ⊢V⦂ A}
          → (W : Γ' ⊢V⦂ B) → U ≐ᵛ U' → sub-atᵛ Θ U W ≐ᵛ sub-atᵛ Θ U' W
sub-atᵛ-≐ Θ W e = castᵛ-≐ _ (sub-≐ᵛ _ (≐ᵛ-refl _) e)

sub-atᶜ-≐ : ∀ {Γ' B C} → (Θ : Ctx) → {M M' : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C}
          → (W : Γ' ⊢V⦂ B) → M ≐ᶜ M' → sub-atᶜ Θ M W ≐ᶜ sub-atᶜ Θ M' W
sub-atᶜ-≐ Θ W e = castᶜ-≐ _ (sub-≐ᶜ _ (≐ᵛ-refl _) e)

------------------------------------------------------------------------
-- THE VARIABLE CASE
--
-- Four positions: in the suffix, the outer entry `B₂`, the inner entry
-- `B₁`, and the prefix `Γ`. The two entries are the content; both are
-- kept in their *unreduced* hit form, as `ren-sub-hit` does, so no
-- normal form for "the value pushed under the suffix" is needed — and
-- with it none of the eternal/non-eternal case analysis at a lock, which
-- `ren-sub-hit` has already absorbed.
------------------------------------------------------------------------

-- Looking up the replaced entry itself.

hitᵛ : ∀ {Γ' B} → (Θ : Ctx) → Γ' ⊢V⦂ B
     → (f : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ) → (Γ' ++ᶜ Θ) ⊢V⦂ B
hitᵛ {Γ'} {B} Θ W f = sub-atᵛ Θ (var f (bvar B Θ)) W

-- The hit at a concatenated suffix is the hit at the outer part, of the
-- value weakened by the inner one. Induction on the outer part, layer by
-- layer, exactly as `ren-sub-hit`; the lock case splits on eternality,
-- since an eternal value crosses a lock by extension rather than by a
-- renaming.

-- Any proof of the context equation will do; the induction never has to
-- reconcile the one it receives with the one it passes down.

Ehit : ∀ {Γ'} → (B B₀ : VType) → (Θ : Ctx)
     → (split-l (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ))
          ++ᶜ split-r (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ)))
     ≡ ((Γ' ∷ B₀) ++ᶜ Θ)
Ehit {Γ'} B B₀ Θ =
  trans (castOf {Γ'} {B} (([] ∷ B₀) ++ᶜ Θ)) (sym (++ᶜ-assoc Γ' ([] ∷ B₀) Θ))

hit-∷-++ᶜ : ∀ {Γ' B B₀} → (Θ : Ctx) → (W : Γ' ⊢V⦂ B)
          → (g  : ¬ Eternal B → ctx-grade (([] ∷ B₀) ++ᶜ Θ) ≾ᵣ uᵣ)
          → (g' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ)
          → (E : (split-l (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ))
                    ++ᶜ split-r (bvar {Γ'} B (([] ∷ B₀) ++ᶜ Θ)))
               ≡ ((Γ' ∷ B₀) ++ᶜ Θ))
          → castᵛ E (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , g
                     ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                        ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)
          ≐ᵛ hitᵛ {Γ' ∷ B₀} Θ (V-rename (wk-ren {A = B₀}) W) g'

hit-∷-++ᶜ {Γ'} {B} {B₀} [] W g g' E = ≡→≐ᵛ (castᵛ-irr E refl _)

hit-∷-++ᶜ {Γ'} {B} {B₀} (Θ ∷ C) W g g' E =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-wk-any E (Ehit B B₀ Θ)
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , g
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (≐ᵛ-trans
      (V-rename-cong wk-ren (hit-∷-++ᶜ Θ W g g' (Ehit B B₀ Θ)))
      (≡→≐ᵛ (sym (cast-wk-any (castOf {Γ' ∷ B₀} {B} (Θ ∷ C))
                              (castOf {Γ' ∷ B₀} {B} Θ) _))))

hit-∷-++ᶜ {Γ'} {B} {B₀} (Θ ⟨ ρ ⟩) W g g' E with eternal? B

... | yes et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ext-any E (Ehit B B₀ Θ) et
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , _
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (≐ᵛ-trans
      (eternal-val-ext-cong et (hit-∷-++ᶜ Θ W _ _ (Ehit B B₀ Θ)))
      (≡→≐ᵛ (sym (cast-ext-any (castOf {Γ' ∷ B₀} {B} (Θ ⟨ ρ ⟩))
                               (castOf {Γ' ∷ B₀} {B} Θ) et _))))

... | no ¬et =
  ≐ᵛ-trans
    (≡→≐ᵛ (cast-ren-⟨⟩-any E (Ehit B B₀ Θ) rn
             (⟨ bvar B (([] ∷ B₀) ++ᶜ Θ) , _
              ⟩[ bvar B (([] ∷ B₀) ++ᶜ Θ)
                 ↦ bval (([] ∷ B₀) ++ᶜ Θ) W ]var)))
    (≐ᵛ-trans (V-rename-cong rn (hit-∷-++ᶜ Θ W _ _ (Ehit B B₀ Θ)))
      (≐ᵛ-trans (V-rename-≐ (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl) _)
                (≡→≐ᵛ (sym (cast-ren-⟨⟩-any (castOf {Γ' ∷ B₀} {B} (Θ ⟨ ρ ⟩))
                                            (castOf {Γ' ∷ B₀} {B} Θ) rn' _)))))
  where
    rn : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (g ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

    rn' : ∀ {Γ₀ : Ctx} → Ren [] Γ₀ (Γ₀ ⟨ ρ ⟩)
    rn' = ⟨⟩-≤-ren (≾ᵣ-zero-productʳ (g' ¬et)) ∘ʳ ⟨⟩-η⁻¹-ren

-- Grade bounds are proof-irrelevant, so the substitution does not see
-- which one it was handed.

bound-irr : ∀ {A ρ} → (f f' : ¬ Eternal A → ρ ≾ᵣ uᵣ) → f ≡ f'
bound-irr f f' = fun-ext (λ z → ≾ᵣ-irrelevant _ _)

castᵛ-fuse : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (V : Γ₁ ⊢V⦂ A)
           → castᵛ e' (castᵛ e V) ≡ castᵛ (trans e e') V
castᵛ-fuse refl refl V = refl

Tgt-cast-fuse : ∀ {Γ₁ Γ₂ Γ₃ A} → (e : Γ₁ ≡ Γ₂) → (e' : Γ₂ ≡ Γ₃) → (t : Tgt Γ₁ A)
              → Tgt-cast e' (Tgt-cast e t) ≡ Tgt-cast (trans e e') t
Tgt-cast-fuse refl refl t = refl

-- Relocating a variable along a context transport, at the `Tgt` level so
-- that the grade travels with the position.

castᵛ-var-tgt : ∀ {Γ Γ' A ρ} → (e : Γ ≡ Γ') → (x : A ∈[ ρ ] Γ)
              → (t : Tgt Γ' A) → Tgt-cast e (ρ , x) ≡ t
              → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
              → (f' : ¬ Eternal A → proj₁ t ≾ᵣ uᵣ)
              → castᵛ e (var f x) ≐ᵛ var f' (proj₂ t)
castᵛ-var-tgt refl x .(_ , x) refl f f' = var-≐

-- The three positions the substitution distinguishes, each taking where
-- the variable sits as a `Tgt` equation.

sub-at-varᵣ : ∀ {Γ' B A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
            → (y : A ∈[ ρ ] ((Γ' ∷ B) ++ᶜ Θ)) → y ≡ ∈-++ᶜʳ {Γ = Γ' ∷ B} x
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ) → (f' : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≐ᵛ var f' (∈-++ᶜʳ {Γ = Γ'} x)
sub-at-varᵣ Θ x _ refl f f' W = sub-var-r Θ x (bval Θ W) f f'

sub-at-varₗ : ∀ {Γ' B A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Γ')
            → (y : A ∈[ grade-++ᶜˡ ρ Θ ] ((Γ' ∷ B) ++ᶜ Θ))
            → y ≡ ∈-++ᶜˡ {Γ = Γ' ∷ B} Θ (Tl-∷ x)
            → (f f' : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ) → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≐ᵛ var f' (∈-++ᶜˡ {Γ = Γ'} Θ x)
sub-at-varₗ Θ x _ refl f f' W = sub-var-l Θ x (bval Θ W) f f'

sub-at-varₕ : ∀ {Γ' B ρ} → (Θ : Ctx) → (y : B ∈[ ρ ] ((Γ' ∷ B) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ' ∷ B) ++ᶜ Θ) B}
                  (ρ , y) (ctx-grade Θ , bvar B Θ)
            → (f : ¬ Eternal B → ρ ≾ᵣ uᵣ)
            → (f' : ¬ Eternal B → ctx-grade Θ ≾ᵣ uᵣ) → (W : Γ' ⊢V⦂ B)
            → sub-atᵛ Θ (var f y) W ≐ᵛ hitᵛ Θ W f'
sub-at-varₕ Θ .(bvar _ Θ) refl f f' W
  rewrite bound-irr f f' = ≐ᵛ-refl _

------------------------------------------------------------------------
-- The four positions.
------------------------------------------------------------------------

swap-var-r : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
           → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ (var f (∈-++ᶜʳ {Γ = Γ ∷ B₁ ∷ B₂} x)) W₂ W₁
swap-var-r {Γ} {B₁} {B₂} Θ x f W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans (sub-atᵛ-≐ Θ W₁ (sub-at-varᵣ Θ x _ refl f f _))
              (sub-at-varᵣ Θ x _ refl f f W₁))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (cong (λ z → _ , z) (∈-++ᶜʳ-assoc (Γ ∷ B₁) ([] ∷ B₂) x))
                      f f))
                (sub-at-varᵣ (([] ∷ B₂) ++ᶜ Θ) (∈-++ᶜʳ {Γ = [] ∷ B₂} x) _
                             refl f f W₁)))
            (castᵛ-var-tgt (assocᴮ⁻ Γ B₂ Θ) _ _
               (cong (λ z → _ , z)
                 (subst-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                             (∈-++ᶜʳ-assoc Γ ([] ∷ B₂) x)))
               f f)))
        (sub-at-varᵣ Θ x _ refl f f W₂)))

swap-var-l : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (v : A ∈[ ρ ] Γ)
           → (f : ¬ Eternal A → grade-++ᶜˡ ρ Θ ≾ᵣ uᵣ)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ (var f (∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ (Tl-∷ (Tl-∷ v))))
                        W₂ W₁
swap-var-l {Γ} {B₁} {B₂} Θ v f W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans (sub-atᵛ-≐ Θ W₁ (sub-at-varₗ Θ (Tl-∷ v) _ refl f f _))
              (sub-at-varₗ Θ v _ refl f f W₁))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                         (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Tl-∷ v)))
                      f fΔ))
                (sub-at-varₗ (([] ∷ B₂) ++ᶜ Θ) v _ refl fΔ fΔ W₁)))
            (castᵛ-var-tgt (assocᴮ⁻ Γ B₂ Θ) _ _
               (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ v) fΔ f)))
        (sub-at-varₗ Θ v _ refl f f W₂)))
  where
    fΔ : ¬ Eternal _ → grade-++ᶜˡ _ (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    fΔ ¬et = subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc _ ([] ∷ B₂) Θ)) (f ¬et)

swap-var-B₂ : ∀ {Γ B₁ B₂ ρ} → (Θ : Ctx)
            → (f : ¬ Eternal B₂ → ρ ≾ᵣ uᵣ)
            → (y : B₂ ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) B₂}
                  (ρ , y) (grade-++ᶜˡ uᵣ Θ , ∈-++ᶜˡ Θ (Hd {Γ = Γ ∷ B₁}))
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-B₂ {Γ} {B₁} {B₂} Θ f .(∈-++ᶜˡ Θ Hd) refl W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans
      (sub-atᵛ-≐ Θ W₁
        (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ (Γ ∷ B₁) B₂ Θ)) f fΘ _))
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₁
          (≐ᵛ-sym (ren-sub-hit (wk-ren {A = B₁}) Θ W₂ fΘ fΘ)))
        (sub-wk-V Θ (hitᵛ Θ W₂ fΘ) (bval Θ W₁))))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (∈-++ᶜˡ-++ᶜʳ (Γ ∷ B₁) ([] ∷ B₂) Θ (Hd {Γ = []}))
                      f f))
                (sub-at-varᵣ (([] ∷ B₂) ++ᶜ Θ)
                             (∈-++ᶜˡ {Γ = [] ∷ B₂} Θ (Hd {Γ = []})) _
                             refl f f W₁)))
            (castᵛ-var-tgt (assocᴮ⁻ Γ B₂ Θ) _ _
               (Tgt-cast-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                  (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ B₂) Θ (Hd {Γ = []})))
               f f)))
        (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ Γ B₂ Θ)) f fΘ W₂)))
  where
    fΘ : ¬ Eternal B₂ → ctx-grade Θ ≾ᵣ uᵣ
    fΘ ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ Θ) (f ¬et)

swap-var-B₁ : ∀ {Γ B₁ B₂ ρ} → (Θ : Ctx)
            → (f : ¬ Eternal B₁ → ρ ≾ᵣ uᵣ)
            → (y : B₁ ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) B₁}
                  (ρ , y) (grade-++ᶜˡ uᵣ Θ , ∈-++ᶜˡ Θ (Tl-∷ (Hd {Γ = Γ})))
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-B₁ {Γ} {B₁} {B₂} Θ f .(∈-++ᶜˡ Θ (Tl-∷ Hd)) refl W₂ W₁ =
  ≐ᵛ-trans
    (≐ᵛ-trans (sub-atᵛ-≐ Θ W₁ (sub-at-varₗ Θ (Hd {Γ = Γ}) _ refl f f _))
              (sub-at-varₕ Θ _ (sym (split→∈-∈-++ᶜˡ Γ B₁ Θ)) f fΘ W₁))
    (≐ᵛ-sym
      (≐ᵛ-trans
        (sub-atᵛ-≐ Θ W₂
          (≐ᵛ-trans
            (castᵛ-≐ (assocᴮ⁻ Γ B₂ Θ)
              (≐ᵛ-trans
                (sub-atᵛ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                   (castᵛ-var-tgt (assocᴮ Γ B₁ B₂ Θ) _ _
                      (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                         (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Hd {Γ = Γ})))
                      f fΔ))
                (sub-at-varₕ (([] ∷ B₂) ++ᶜ Θ) _
                   (sym (split→∈-∈-++ᶜˡ Γ B₁ (([] ∷ B₂) ++ᶜ Θ))) fΔ g W₁)))
            (≐ᵛ-trans
              (≡→≐ᵛ (castᵛ-fuse (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                                (assocᴮ⁻ Γ B₂ Θ) _))
              (hit-∷-++ᶜ Θ W₁ g fΘ (Ehit B₁ B₂ Θ)))))
        (≐ᵛ-trans
          (sub-atᵛ-≐ Θ W₂ (≐ᵛ-sym (ren-sub-hit (wk-ren {A = B₂}) Θ W₁ fΘ fΘ)))
          (sub-wk-V Θ (hitᵛ Θ W₁ fΘ) (bval Θ W₂)))))
  where
    fΘ : ¬ Eternal B₁ → ctx-grade Θ ≾ᵣ uᵣ
    fΘ ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ Θ) (f ¬et)

    fΔ : ¬ Eternal B₁ → grade-++ᶜˡ uᵣ (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    fΔ ¬et = subst (_≾ᵣ uᵣ) (sym (grade-++ᶜˡ-assoc uᵣ ([] ∷ B₂) Θ)) (f ¬et)

    g : ¬ Eternal B₁ → ctx-grade (([] ∷ B₂) ++ᶜ Θ) ≾ᵣ uᵣ
    g ¬et = subst (_≾ᵣ uᵣ) (grade-++ᶜˡ-uᵣ (([] ∷ B₂) ++ᶜ Θ)) (fΔ ¬et)

-- The prefix case, taking the equation in the shape `∈-++ᶜ-split-inj₁`
-- delivers it.

swap-var-l′ : ∀ {Γ B₁ B₂ A ρ ρ'} → (Θ : Ctx) → (v : A ∈[ ρ' ] Γ)
            → (y : A ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → _≡_ {A = Tgt ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) A}
                  (ρ , y) (grade-++ᶜˡ ρ' Θ , ∈-++ᶜˡ Θ (Tl-∷ (Tl-∷ v)))
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-l′ Θ v .(∈-++ᶜˡ Θ (Tl-∷ (Tl-∷ v))) refl f W₂ W₁ =
  swap-var-l Θ v f W₂ W₁

swap-var-r′ : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx) → (x : A ∈[ ρ ] Θ)
            → (y : A ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
            → y ≡ ∈-++ᶜʳ {Γ = Γ ∷ B₁ ∷ B₂} x
            → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
            → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
            → SubSwapV Θ (var f y) W₂ W₁
swap-var-r′ Θ x .(∈-++ᶜʳ x) refl f W₂ W₁ = swap-var-r Θ x f W₂ W₁

-- Where the variable sits decides which of the four applies.

sub-swap-var : ∀ {Γ B₁ B₂ A ρ} → (Θ : Ctx)
             → (y : A ∈[ ρ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
             → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
             → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
             → SubSwapV Θ (var f y) W₂ W₁

sub-swap-var {Γ} {B₁} {B₂} Θ y f W₂ W₁
  with ∈-++ᶜ-split (Γ ∷ B₁ ∷ B₂) Θ y in eq

... | inj₂ x =
  swap-var-r′ Θ x y (∈-++ᶜ-split-inj₂ (Γ ∷ B₁ ∷ B₂) Θ y x eq) f W₂ W₁

... | inj₁ (ρ' , Hd) =
  swap-var-B₂ Θ f y (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ y Hd eq) W₂ W₁

... | inj₁ (ρ' , Tl-∷ Hd) =
  swap-var-B₁ Θ f y (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ y (Tl-∷ Hd) eq) W₂ W₁

... | inj₁ (ρ' , Tl-∷ (Tl-∷ v)) =
  swap-var-l′ Θ v y
    (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ y (Tl-∷ (Tl-∷ v)) eq) f W₂ W₁

------------------------------------------------------------------------
-- THE CELL AN `unbox` NAMES
--
-- `sub-unbox` rebuilds an unboxing from the cell the substitution leaves,
-- so the `unbox` case reduces to: the two orders name the same cell. That
-- is the `rvar` counterpart of the variable case, and a simpler one — a
-- box type is never eternal, so `⟨_⟩[_↦_]rvar` has no `eternal?` split
-- and each position is one `Tgt-cast` push.
------------------------------------------------------------------------

-- The cell left by replacing the entry at the boundary.

rcell : ∀ {Γ' B A ρ σ} → (Θ : Ctx)
      → ([ ρ ] A ∈[ σ ] ((Γ' ∷ B) ++ᶜ Θ)) → (W : Γ' ⊢V⦂ B)
      → Tgt (Γ' ++ᶜ Θ) ([ ρ ] A)
rcell {Γ'} {B} Θ c W =
  Tgt-cast (castOf {Γ'} {B} Θ) (rvar-tgt c (bvar B Θ) (bval Θ W))

-- The same at an already-located cell. `Tgt` is a Σ, so `cong` cannot infer
-- the dependent motive from a lambda — this has to be named, exactly as
-- `var-tgt′` is.

rcell′ : ∀ {Γ' B A ρ} → (Θ : Ctx) → Tgt ((Γ' ∷ B) ++ᶜ Θ) ([ ρ ] A)
       → (W : Γ' ⊢V⦂ B) → Tgt (Γ' ++ᶜ Θ) ([ ρ ] A)
rcell′ Θ (σ , c) W = rcell Θ c W

-- and, when the entry replaced *is* the cell, the cell of the value it is
-- replaced by, pushed under the suffix.

hcell : ∀ {Γ' A ρ} → (Θ : Ctx) → (W : Γ' ⊢V⦂ [ ρ ] A) → Tgt (Γ' ++ᶜ Θ) ([ ρ ] A)
hcell {Γ'} {A} {ρ} Θ W = rcell Θ (bvar ([ ρ ] A) Θ) W

-- The cell counterpart of `hit-∷-++ᶜ`, and by the same induction.

rhit-∷-++ᶜ : ∀ {Γ' A ρ B₀} → (Θ : Ctx) → (W : Γ' ⊢V⦂ [ ρ ] A)
           → (E : (split-l (bvar {Γ'} ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                     ++ᶜ split-r (bvar {Γ'} ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ)))
                ≡ ((Γ' ∷ B₀) ++ᶜ Θ))
           → Tgt-cast E
               (rvar-tgt (bvar ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                         (bvar ([ ρ ] A) (([] ∷ B₀) ++ᶜ Θ))
                         (bval (([] ∷ B₀) ++ᶜ Θ) W))
           ≡ hcell {Γ' ∷ B₀} Θ (V-rename (wk-ren {A = B₀}) W)

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} [] (var f y) E =
  Tgt-cast-irr E refl _

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} (Θ ∷ C) W E =
  trans (Tgt-cast-irr E (cong (_∷ C) (Ehit ([ ρ ] A) B₀ Θ)) _)
    (trans (Tgt-cast-∷ (Ehit ([ ρ ] A) B₀ Θ) _)
      (trans (cong Tgt-∷ (rhit-∷-++ᶜ Θ W (Ehit ([ ρ ] A) B₀ Θ)))
        (trans (sym (Tgt-cast-∷ (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ) _))
               (Tgt-cast-irr (cong (_∷ C) (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ))
                             (castOf {Γ' ∷ B₀} {[ ρ ] A} (Θ ∷ C)) _))))

rhit-∷-++ᶜ {Γ'} {A} {ρ} {B₀} (Θ ⟨ ρ' ⟩) W E =
  trans (Tgt-cast-irr E (cong (_⟨ ρ' ⟩) (Ehit ([ ρ ] A) B₀ Θ)) _)
    (trans (Tgt-cast-⟨⟩ ρ' (Ehit ([ ρ ] A) B₀ Θ) _)
      (trans (cong (Tgt-⟨⟩ ρ') (rhit-∷-++ᶜ Θ W (Ehit ([ ρ ] A) B₀ Θ)))
        (trans (sym (Tgt-cast-⟨⟩ ρ' (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ) _))
               (Tgt-cast-irr (cong (_⟨ ρ' ⟩) (castOf {Γ' ∷ B₀} {[ ρ ] A} Θ))
                             (castOf {Γ' ∷ B₀} {[ ρ ] A} (Θ ⟨ ρ' ⟩)) _))))

-- The four positions, at the cell level.

unbox-cell-swap : ∀ {Γ B₁ B₂ A ρ σ} → (Θ : Ctx)
                → (c : [ ρ ] A ∈[ σ ] ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → rcell Θ (proj₂ (rcell Θ c (V-rename (wk-ren {A = B₁}) W₂)))
                          W₁
                ≡ rcell Θ
                    (proj₂ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ)
                             (rcell (([] ∷ B₂) ++ᶜ Θ)
                                (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) (σ , c)))
                                W₁)))
                    W₂

unbox-cell-swap {Γ} {B₁} {B₂} {A} {ρ} {σ} Θ c W₂ W₁
  with ∈-++ᶜ-split (Γ ∷ B₁ ∷ B₂) Θ c in eqc

... | inj₂ c'
  rewrite ∈-++ᶜ-split-inj₂ (Γ ∷ B₁ ∷ B₂) Θ c c' eqc =
  trans (cong (λ t → rcell′ Θ t W₁)
              (sub-rvar-r {Γ = Γ ∷ B₁} {B = B₂} Θ c'
                          (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
    (trans (sub-rvar-r {Γ = Γ} {B = B₁} Θ c' (bval Θ W₁))
      (sym
        (trans
          (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
            (trans
              (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (cong (λ z → σ , z)
                          (∈-++ᶜʳ-assoc (Γ ∷ B₁) ([] ∷ B₂) c')))
              (sub-rvar-r {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ)
                          (∈-++ᶜʳ {Γ = [] ∷ B₂} c')
                          (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
          (trans
            (cong (λ t → rcell′ Θ t W₂)
                  (cong (λ z → σ , z)
                        (subst-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                                    (∈-++ᶜʳ-assoc Γ ([] ∷ B₂) c'))))
            (sub-rvar-r {Γ = Γ} {B = B₂} Θ c' (bval Θ W₂))))))

... | inj₁ (σ' , c') =
  subst (λ t → rcell Θ (proj₂ (rcell Θ (proj₂ t)
                                (V-rename (wk-ren {A = B₁}) W₂))) W₁
             ≡ rcell Θ
                 (proj₂ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ)
                          (rcell (([] ∷ B₂) ++ᶜ Θ)
                             (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) t)) W₁)))
                 W₂)
        (sym (∈-++ᶜ-split-inj₁ (Γ ∷ B₁ ∷ B₂) Θ c c' eqc))
        (go c')
  where
    go : ∀ {σ₀} → (c₀ : [ ρ ] A ∈[ σ₀ ] (Γ ∷ B₁ ∷ B₂))
       → rcell Θ (proj₂ (rcell Θ (∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ c₀)
                          (V-rename (wk-ren {A = B₁}) W₂))) W₁
       ≡ rcell Θ
           (proj₂ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ)
                    (rcell (([] ∷ B₂) ++ᶜ Θ)
                       (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ)
                                (_ , ∈-++ᶜˡ {Γ = Γ ∷ B₁ ∷ B₂} Θ c₀)))
                       W₁)))
           W₂

    -- the cell is the outer entry `B₂`: the left order hits it at once and
    -- then cancels the weakening (`unbox-cell-wk`); the right order lets it
    -- survive into the suffix and hits it last
    go Hd =
      trans
        (cong (λ t → rcell′ Θ t W₁)
          (trans (cong (λ t → rcell′ Θ t (V-rename (wk-ren {A = B₁}) W₂))
                       (sym (split→∈-∈-++ᶜˡ (Γ ∷ B₁) B₂ Θ)))
                 (sym (rvar-hit-ren (wk-ren {A = B₁}) Θ W₂))))
        (trans (unbox-cell-wk {Γ = Γ} {B = B₁} Θ (proj₂ (hcell Θ W₂)) (bval Θ W₁))
          (sym
            (trans
              (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                        (∈-++ᶜˡ-++ᶜʳ (Γ ∷ B₁) ([] ∷ B₂) Θ (Hd {Γ = []})))
                  (sub-rvar-r {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ)
                              (∈-++ᶜˡ {Γ = [] ∷ B₂} Θ (Hd {Γ = []}))
                              (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
              (trans
                (cong (λ t → rcell′ Θ t W₂)
                  (Tgt-cast-flip (++ᶜ-assoc Γ ([] ∷ B₂) Θ) _ _
                     (∈-++ᶜˡ-++ᶜʳ Γ ([] ∷ B₂) Θ (Hd {Γ = []}))))
                (cong (λ t → rcell′ Θ t W₂)
                      (sym (split→∈-∈-++ᶜˡ Γ B₂ Θ)))))))

    -- the cell is the inner entry `B₁`: the left order lets it survive and
    -- then hits it; the right order hits it at the bigger suffix, and
    -- `rhit-∷-++ᶜ` peels the `B₂` layer off again
    go (Tl-∷ Hd) =
      trans
        (cong (λ t → rcell′ Θ t W₁)
              (sub-rvar-l {Γ = Γ ∷ B₁} {B = B₂} Θ (Hd {Γ = Γ})
                          (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
        (trans
          (cong (λ t → rcell′ Θ t W₁)
                (sym (split→∈-∈-++ᶜˡ Γ B₁ Θ)))
          (sym
            (trans
              (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                       (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Hd {Γ = Γ}))))
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                        (sym (split→∈-∈-++ᶜˡ Γ B₁ (([] ∷ B₂) ++ᶜ Θ))))))
              (trans
                (cong (λ t → rcell′ Θ t W₂)
                  (trans (Tgt-cast-fuse (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                                        (assocᴮ⁻ Γ B₂ Θ) _)
                         (rhit-∷-++ᶜ Θ W₁ (Ehit B₁ B₂ Θ))))
                (trans
                  (cong (λ t → rcell′ Θ t W₂)
                        (sym (rvar-hit-ren (wk-ren {A = B₂}) Θ W₁)))
                  (unbox-cell-wk {Γ = Γ} {B = B₂} Θ (proj₂ (hcell Θ W₁)) (bval Θ W₂)))))))

    go (Tl-∷ (Tl-∷ c₀)) =
      trans (cong (λ t → rcell′ Θ t W₁)
                  (sub-rvar-l {Γ = Γ ∷ B₁} {B = B₂} Θ (Tl-∷ c₀)
                              (bval Θ (V-rename (wk-ren {A = B₁}) W₂))))
        (trans (sub-rvar-l {Γ = Γ} {B = B₁} Θ c₀ (bval Θ W₁))
          (sym
            (trans
              (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                (trans
                  (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                    (Tgt-cast-flip⁻ (++ᶜ-assoc (Γ ∷ B₁) ([] ∷ B₂) Θ) _ _
                       (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ (Tl-∷ c₀))))
                  (sub-rvar-l {Γ = Γ} {B = B₁} (([] ∷ B₂) ++ᶜ Θ) c₀
                              (bval (([] ∷ B₂) ++ᶜ Θ) W₁))))
              (trans
                (cong (λ t → rcell′ Θ t W₂)
                      (∈-++ᶜˡ-assoc ([] ∷ B₂) Θ c₀))
                (sub-rvar-l {Γ = Γ} {B = B₂} Θ c₀ (bval Θ W₂))))))

-- `unbox`: both orders rebuild the unboxing from the cell the substitution
-- leaves (`sub-unbox`), so `unbox-≐` reduces the case to `unbox-cell-swap`
-- for the cell and the induction hypothesis for the body.

sub-swap-unbox : ∀ {Γ B₁ B₂ A C ρ Δ₀} → (Θ : Ctx)
               → (w : Ren [] (Δ₀ ⟨ ρ ⟩) ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
               → (V : Δ₀ ⊢V⦂ [ ρ ] A)
               → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ∷ A ⊢C⦂ C)
               → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
               → SubSwapC (Θ ∷ A) M W₂ W₁
               → SubSwapC Θ (unbox w V M) W₂ W₁

sub-swap-unbox {Γ} {B₁} {B₂} {A} {C} {ρ} {Δ₀} Θ w V M W₂ W₁ ih =
  ≐ᶜ-trans
    (≐ᶜ-trans
      (sub-atᶜ-≐ Θ W₁
        (≐ᶜ-trans (castᶜ-≐ (castOf {Γ ∷ B₁} {B₂} Θ)
                     (sub-unbox w V M x₂ V₂ relA))
                  (≡→≐ᶜ (cast-unbox (castOf {Γ ∷ B₁} {B₂} Θ)))))
      (≐ᶜ-trans (castᶜ-≐ (castOf {Γ} {B₁} Θ)
                   (sub-unbox wA hd bodyA x₁ V₁ relB))
                (≡→≐ᶜ (cast-unbox (castOf {Γ} {B₁} Θ)))))
    (≐ᶜ-trans
      (unbox-≐ cell
        (≐ᶜ-trans
          (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (castOf {Γ} {B₁} Θ))
                           (castOf {Γ} {B₁} (Θ ∷ A)) _))
          (≐ᶜ-trans
            (sub-atᶜ-≐ (Θ ∷ A) W₁
              (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (castOf {Γ ∷ B₁} {B₂} Θ))
                               (castOf {Γ ∷ B₁} {B₂} (Θ ∷ A)) _)))
            (≐ᶜ-trans ih
              (≐ᶜ-trans
                (sub-atᶜ-≐ (Θ ∷ A) W₂
                  (≡→≐ᶜ (trans
                    (cong (castᶜ (assocᴮ⁻ Γ B₂ (Θ ∷ A)))
                      (castᶜ-irr (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ (Θ ∷ A)))
                                 (cong (_∷ A)
                                       (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))) _))
                    (castᶜ-irr (assocᴮ⁻ Γ B₂ (Θ ∷ A))
                               (cong (_∷ A) (assocᴮ⁻ Γ B₂ Θ)) _))))
                (≡→≐ᶜ (castᶜ-irr (castOf {Γ} {B₂} (Θ ∷ A))
                                 (cong (_∷ A) (castOf {Γ} {B₂} Θ)) _)))))))
      (≐ᶜ-sym
        (≐ᶜ-trans
          (sub-atᶜ-≐ Θ W₂
            (≐ᶜ-trans
              (castᶜ-≐ (assocᴮ⁻ Γ B₂ Θ)
                (≐ᶜ-trans
                  (sub-atᶜ-≐ (([] ∷ B₂) ++ᶜ Θ) W₁
                    (≡→≐ᶜ (cast-unbox (assocᴮ Γ B₁ B₂ Θ))))
                  (≐ᶜ-trans
                    (castᶜ-≐ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                      (sub-unbox (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V _ y₁ U₁ relC))
                    (≡→≐ᶜ (cast-unbox
                             (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)))))))
              (≡→≐ᶜ (cast-unbox (assocᴮ⁻ Γ B₂ Θ)))))
          (≐ᶜ-trans
            (castᶜ-≐ (castOf {Γ} {B₂} Θ)
              (sub-unbox (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd _ y₂ U₂ relD))
            (≡→≐ᶜ (cast-unbox (castOf {Γ} {B₂} Θ)))))))
  where
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    x₂ = bvar B₂ Θ
    V₂ = bval Θ Ŵ₂
    x₁ = bvar B₁ Θ
    V₁ = bval Θ W₁
    y₁ = bvar B₁ (([] ∷ B₂) ++ᶜ Θ)
    U₁ = bval (([] ∷ B₂) ++ᶜ Θ) W₁
    y₂ = bvar B₂ Θ
    U₂ = bval Θ W₂

    cW = proj₂ (unbox-tgt w V)

    hd : ∀ {Γ₀ : Ctx} → (Γ₀ ∷ [ ρ ] A) ⊢V⦂ [ ρ ] A
    hd = var (λ _ → ≾ᵣ-refl) Hd

    relA = ≾ᵣ-trans (proj₂ (proj₂ (⟨ cW ⟩[ x₂ ↦ V₂ ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var w V)))

    vA = proj₂ (rvar-tgt cW x₂ V₂)

    wA = castʳᵉ (castOf {Γ ∷ B₁} {B₂} Θ) (unbox-var-ren vA relA)

    bodyA = castᶜ (cong (_∷ A) (castOf {Γ ∷ B₁} {B₂} Θ))
                  (M [ Tl-∷ x₂ ↦ V₂ ]c)

    relB = ≾ᵣ-trans (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt wA hd) ⟩[ x₁ ↦ V₁ ]rvar)))
                    (proj₂ (proj₂ (unbox⇒var wA hd)))

    vB = proj₂ (rvar-tgt (proj₂ (unbox-tgt wA hd)) x₁ V₁)

    wB = castʳᵉ (castOf {Γ} {B₁} Θ) (unbox-var-ren vB relB)

    relC = ≾ᵣ-trans
             (proj₂ (proj₂
               (⟨ proj₂ (unbox-tgt (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V)
                ⟩[ y₁ ↦ U₁ ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V)))

    vC = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w) V))
                         y₁ U₁)

    wC = castʳᵉ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)) (unbox-var-ren vC relC)

    relD = ≾ᵣ-trans
             (proj₂ (proj₂
               (⟨ proj₂ (unbox-tgt (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd)
                ⟩[ y₂ ↦ U₂ ]rvar)))
             (proj₂ (proj₂ (unbox⇒var (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd)))

    vD = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC) hd))
                         y₂ U₂)

    wD = castʳᵉ (castOf {Γ} {B₂} Θ) (unbox-var-ren vD relD)

    -- each stored renaming is read only through `unbox-tgt`, and there it is
    -- the cell the substitution left; so the two sides' cells are exactly the
    -- two sides of `unbox-cell-swap`
    cellA : unbox-tgt wA hd ≡ rcell Θ cW Ŵ₂
    cellA = trans (unbox-tgt-castʳᵉ (castOf {Γ ∷ B₁} {B₂} Θ)
                                    (unbox-var-ren vA relA) hd)
                  (cong (Tgt-cast (castOf {Γ ∷ B₁} {B₂} Θ))
                        (unbox-var-tgt vA relA))

    cellC : unbox-tgt wC hd
          ≡ rcell (([] ∷ B₂) ++ᶜ Θ)
                  (proj₂ (Tgt-cast (assocᴮ Γ B₁ B₂ Θ) (unbox-tgt w V))) W₁
    cellC =
      trans (unbox-tgt-castʳᵉ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
                              (unbox-var-ren vC relC) hd)
        (trans (cong (Tgt-cast (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ)))
                     (unbox-var-tgt vC relC))
               (cong (λ t → rcell′ (([] ∷ B₂) ++ᶜ Θ) t W₁)
                     (unbox-tgt-castʳᵉ (assocᴮ Γ B₁ B₂ Θ) w V)))

    cell : unbox-tgt wB hd ≡ unbox-tgt wD hd
    cell =
      trans (unbox-tgt-castʳᵉ (castOf {Γ} {B₁} Θ) (unbox-var-ren vB relB) hd)
        (trans (cong (Tgt-cast (castOf {Γ} {B₁} Θ)) (unbox-var-tgt vB relB))
          (trans (cong (λ t → rcell′ Θ t W₁) cellA)
            (trans (unbox-cell-swap Θ cW W₂ W₁)
              (sym
                (trans (unbox-tgt-castʳᵉ (castOf {Γ} {B₂} Θ)
                                         (unbox-var-ren vD relD) hd)
                  (trans (cong (Tgt-cast (castOf {Γ} {B₂} Θ))
                               (unbox-var-tgt vD relD))
                    (trans
                      (cong (λ t → rcell′ Θ t W₂)
                            (unbox-tgt-castʳᵉ (assocᴮ⁻ Γ B₂ Θ) wC hd))
                      (cong (λ t → rcell′ Θ (Tgt-cast (assocᴮ⁻ Γ B₂ Θ) t) W₂)
                            cellC))))))))

-- `handle`: the scrutinee and the sequel are the induction hypotheses at
-- their own suffixes, so the whole content is the clauses — the same swap
-- at the *restricted* context, where each order reaches them through its
-- own `⟨_⟩[_↦_]cl`.
--
-- That is the one piece still open. It dispatches on `eternal? B₁` and
-- `eternal? B₂` (four combinations, by `cl-cancel`'s Dec-argument
-- pattern, since a `with` would abstract the clause family's own type).
-- Three are cheap: a `⟨ no ¬et ⟩cl` is a transport, so at most one
-- substitution survives on each side and the leftover transports form a
-- loop that `uip` collapses (`sub-wk-handle-ne`'s `collapse`). The
-- both-eternal one is *this lemma again* at the splitting's own halves,
-- threaded through a `sub-swap-C-cast` so the recursion stays on the bare
-- clause — `sub-wk-handle-et`'s shape, and the same reason: only there do
-- the two ways of naming the substituted variable become the same
-- splitting (`split→∈-unique`/`split→∈-unique₂`).

-- The clause action with the eternality decision taken as an argument, so
-- that the four branches can be matched rather than `with`-abstracted —
-- a `with` would abstract the clause family's own type, which mentions
-- `_ᴱ` of the very context being decided about.

sub-atᴴ′ : ∀ {Γ' B D} → Dec (Eternal B) → (Θ : Ctx)
         → Fam D (((Γ' ∷ B) ++ᶜ Θ) ᴱ) → Γ' ⊢V⦂ B → Fam D ((Γ' ++ᶜ Θ) ᴱ)
sub-atᴴ′ {Γ'} {B} dec Θ H W op ε =
  Cl-cast op ε (castOf {Γ'} {B} Θ) (⟨ dec ⟩[ bvar B Θ ↦ bval Θ W ]cl H op ε)

inner₀ᴴ′ : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → (Θ : Ctx)
         → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₁
         → Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
inner₀ᴴ′ {Γ} {B₁} {B₂} dec₁ Θ H W₁ op ε =
  Cl-cast op ε (assocᴮ⁻ Γ B₂ Θ)
    (sub-atᴴ′ dec₁ (([] ∷ B₂) ++ᶜ Θ)
       (λ op' ε' → Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')) W₁ op ε)

outerᴴ′ : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → Dec (Eternal B₂) → (Θ : Ctx)
        → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁
        → Fam D ((Γ ++ᶜ Θ) ᴱ)
outerᴴ′ {B₁ = B₁} dec₁ dec₂ Θ H W₂ W₁ =
  sub-atᴴ′ dec₁ Θ (sub-atᴴ′ dec₂ Θ H (V-rename (wk-ren {A = B₁}) W₂)) W₁

innerᴴ′ : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → Dec (Eternal B₂) → (Θ : Ctx)
        → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁
        → Fam D ((Γ ++ᶜ Θ) ᴱ)
innerᴴ′ dec₁ dec₂ Θ H W₂ W₁ =
  sub-atᴴ′ dec₂ Θ (inner₀ᴴ′ dec₁ Θ H W₁) W₂

ClSwap : ∀ {Γ B₁ B₂ D} → Dec (Eternal B₁) → Dec (Eternal B₂) → (Θ : Ctx)
       → Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ) → Γ ⊢V⦂ B₂ → Γ ⊢V⦂ B₁
       → (op : Op) → (ε : E) → Set
ClSwap dec₁ dec₂ Θ H W₂ W₁ op ε =
  outerᴴ′ dec₁ dec₂ Θ H W₂ W₁ op ε ≐ᶜ innerᴴ′ dec₁ dec₂ Θ H W₂ W₁ op ε

------------------------------------------------------------------------
-- BEING A TRANSPORT OF A GIVEN TERM
--
-- Every clause-level step that does not substitute is a transport, of one
-- of two shapes (`Cl-cast`, and `⟨ no ¬et ⟩cl`'s own `subst` at the
-- `_++ᶜ D` motive). Recording "X is some transport of h" makes them
-- compose, and two such records of the same `h` are equal by `uip` —
-- which is the whole of the both-non-eternal branch.
------------------------------------------------------------------------

IsSub : ∀ {Γ₀ Γ₁ C} → Γ₀ ⊢C⦂ C → Γ₁ ⊢C⦂ C → Set
IsSub {Γ₀} {Γ₁} {C} h X = Σ[ e ∈ Γ₀ ≡ Γ₁ ] X ≡ subst (_⊢C⦂ C) e h

isSub-refl : ∀ {Γ₀ C} → (h : Γ₀ ⊢C⦂ C) → IsSub h h
isSub-refl h = refl , refl

isSub-substC : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → (X : Γ₁ ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X → IsSub h (subst (_⊢C⦂ C) e X)
isSub-substC {C = C} {h = h} X e (e₀ , q) =
  trans e₀ e
  , trans (cong (subst (_⊢C⦂ C) e) q) (subst-fuseᶜ e₀ e h)

isSub-cast : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → (X : Γ₁ ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
           → IsSub h X → IsSub h (castᶜ e X)
isSub-cast {C = C} X e p =
  subst (IsSub _) (sym (castᶜ≡subst e X)) (isSub-substC X e p)

-- the two shapes the clause level actually presents

isSub-Cl : ∀ {Γ₀ Γ₁ Γ₂ D} → (op : Op) → (ε : E)
         → {h : Γ₀ ⊢C⦂ D ‼ (op-grade op ·ₑ ε)}
         → (X : Cl D op ε (Γ₁ ᴱ)) → (e : Γ₁ ≡ Γ₂)
         → IsSub h X → IsSub h (Cl-cast op ε e X)
isSub-Cl {D = D} op ε X e p =
  isSub-cast X
    (cong (λ Γ₃ → Γ₃ ᴱ ∷ type-of-gtype (param op)
                     ∷ [ mapᵉ (op-grade op) ]
                         (type-of-gtype (arity op) ⇒ D ‼ ε))
          e)
    p

-- the shape `⟨ no ¬et ⟩[_↦_]cl` transports at
isSub-substD : ∀ {Γ₀ Γ₁ Γ₂ C} → (Dc : Ctx) → {h : Γ₀ ⊢C⦂ C}
             → (X : (Γ₁ ++ᶜ Dc) ⊢C⦂ C) → (e : Γ₁ ≡ Γ₂)
             → IsSub h X
             → IsSub h (subst (λ Γ₃ → (Γ₃ ++ᶜ Dc) ⊢C⦂ C) e X)
isSub-substD Dc X e p =
  subst (IsSub _) (sym (subst-++ᶜʳ Dc e X))
        (isSub-substC X (cong (_++ᶜ Dc) e) p)

-- two transports of one term are transports of each other

isSub-reassoc : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
              → IsSub h X → IsSub h Y → IsSub Y X
isSub-reassoc {C = C} {h = h} (e , q) (e' , q') =
  trans (sym e') e
  , trans q
      (trans (cong (λ z → subst (_⊢C⦂ C) z h)
                   (uip {p = e} {q = trans e' (trans (sym e') e)}))
        (trans (sym (subst-fuseᶜ e' (trans (sym e') e) h))
               (cong (subst (_⊢C⦂ C) (trans (sym e') e)) (sym q'))))

isSub-trans : ∀ {Γ₀ Γ₁ Γ₂ C} → {h : Γ₀ ⊢C⦂ C} → {X : Γ₁ ⊢C⦂ C} → {Y : Γ₂ ⊢C⦂ C}
            → IsSub h X → IsSub X Y → IsSub h Y
isSub-trans {C = C} {h = h} (e , q) (e' , q') =
  trans e e'
  , trans q' (trans (cong (subst (_⊢C⦂ C) e') q) (subst-fuseᶜ e e' h))

isSub-uniq : ∀ {Γ₀ Γ₁ C} → {h : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
           → IsSub h X → IsSub h Y → X ≡ Y
isSub-uniq {C = C} {h = h} (e , q) (e' , q') =
  trans q (trans (cong (λ z → subst (_⊢C⦂ C) z h) (uip {p = e} {q = e'}))
                 (sym q'))

-- BOTH ENTRIES NON-ETERNAL
--
-- Neither `⟨ no ¬et ⟩cl` substitutes, so each side is a tower of
-- transports over the same clause: four on the left, six on the right.

cl-swap-nn : ∀ {Γ B₁ B₂ D} → (¬et₁ : ¬ Eternal B₁) → (¬et₂ : ¬ Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε

cl-swap-nn {Γ} {B₁} {B₂} {D} ¬et₁ ¬et₂ Θ H W₂ W₁ op ε =
  ≡→≐ᶜ (isSub-uniq lhs rhs)
  where
    Dc = Dcl D op ε

    lhs : IsSub (H op ε) (outerᴴ′ (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
        (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ Θ))
          (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
              (isSub-refl (H op ε)))))

    rhs : IsSub (H op ε) (innerᴴ′ (no ¬et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
        (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
          (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
            (isSub-Cl op ε _ (castOf {Γ} {B₁} (([] ∷ B₂) ++ᶜ Θ))
              (isSub-substD Dc _
                (ᴱ-drop-split ¬et₁ (bvar B₁ (([] ∷ B₂) ++ᶜ Θ)))
                (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ)
                          (isSub-refl (H op ε)))))))

-- `sub-atᶜ` is natural in a transport of its prefix, its suffix, its term
-- and its value — which is what the eternal branches need, `cl-yes`
-- landing the two sides at contexts that agree only propositionally.
-- Proved by matching the two context equations; the `IsSub` premise then
-- forces the terms equal, its own equation being a loop.

sub-at-IsSub : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
             → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C)
             → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
             → IsSub X₁ X₂
             → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
             → subst (_⊢V⦂ B) eΓ V₁ ≡ V₂
             → IsSub (sub-atᶜ Θ₁ X₁ V₁) (sub-atᶜ Θ₂ X₂ V₂)
sub-at-IsSub refl refl X₁ X₂ (e , q) V .V refl =
  refl , cong (λ z → sub-atᶜ _ z V) (trans q (subst-loopᶜ e X₁))

-- The eternal restriction respects a transport of its context.

restrict-substᵛ : ∀ {Γ₁ Γ₂ A} → (e : Γ₁ ≡ Γ₂) → (et : Eternal A) → (V : Γ₁ ⊢V⦂ A)
                → eternal-val-restrict et (subst (_⊢V⦂ A) e V)
                ≡ subst (_⊢V⦂ A) (cong _ᴱ e) (eternal-val-restrict et V)
restrict-substᵛ refl et V = refl

------------------------------------------------------------------------
-- WHAT `⟨ yes et ⟩[_↦_]cl` REALLY IS
--
-- It is `sub-atᶜ` at the *restricted* contexts — but at the splitting's
-- own halves (`split-l x ᴱ`, `split-r x ᴱ ++ᶜ Dcl`), not at the contexts
-- those are propositionally equal to. That is `sub-wk-handle-et`'s
-- hard-won move, and the reason for it is the same: only there do
-- `split-++ʳ (∈-ᴱ-split et x) Dcl` and `split-≡-++ᶜ` have literally the
-- same halves, so `split→∈-unique` applies on the nose.
--
-- Both `⟨ yes et ⟩cl` and that `sub-atᶜ` are transports of one and the
-- same substituted clause, which is what the two lemmas below record;
-- `isSub-uniq` then identifies them.
------------------------------------------------------------------------

-- the substituted clause both sides are transports of

clBody : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (split-l (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))
            ++ᶜ split-r (split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
         ⊢C⦂ D ‼ (op-grade op ·ₑ ε)
clBody {D = D} et x W H op ε =
  (H op ε) [ split→∈ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))
             ↦ subst (_⊢V⦂ _)
                 (sym (split→∈-split-l
                        (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε))))
                 (eternal-val-restrict et W) ]c

-- the clause substitution is that, transported (definitionally)

cl-yes-raw : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → IsSub (clBody et x W H op ε) (⟨ yes et ⟩[ x ↦ W ]cl H op ε)
cl-yes-raw et x W H op ε = _ , refl

-- and so is the `sub-atᶜ` at the splitting's own halves

cl-yes-sub : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
           → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
           → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
                ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
           → IsSub (clBody et x W H op ε)
                   (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                            (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                            (eternal-val-restrict et W))
cl-yes-sub {Γ₀} {A} {ρ} {D} et x W H op ε e =
  isSub-cast _ (castOf {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε))
    (_ , sub-cast-C′ e (H op ε) v y ey U U' eU)
  where
    Dc = Dcl D op ε
    Γ₀' = split-l x ᴱ
    Θ₀' = split-r x ᴱ ++ᶜ Dc

    s = split-++ʳ (∈-ᴱ-split et x) Dc
    v = split→∈ s
    y = split→∈ (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})

    ey : subst (λ Γ₁ → A ∈[ ctx-grade Θ₀' ] Γ₁) e v ≡ y
    ey = split→∈-unique e s (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})

    U : split-l v ⊢V⦂ A
    U = subst (_⊢V⦂ A) (sym (split→∈-split-l s)) (eternal-val-restrict et W)

    U' : split-l y ⊢V⦂ A
    U' = bval Θ₀' (eternal-val-restrict et W)

    eU : subst (_⊢V⦂ A) (trans (split-l-cast e v) (cong split-l ey)) U ≡ U'
    eU =
      trans (subst-fuseᵛ (sym (split→∈-split-l s))
                         (trans (split-l-cast e v) (cong split-l ey))
                         (eternal-val-restrict et W))
        (trans (substᵛ-irr _
                  (sym (split→∈-split-l (split-≡-++ᶜ {Γ₀' ∷ A} {Θ₀'})))
                  (eternal-val-restrict et W))
               (sym (castᵛ≡subst _ (eternal-val-restrict et W))))

-- hence the clause substitution *is* that `sub-atᶜ`, transported

cl-yes : ∀ {Γ₀ A ρ D} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀)
       → (W : split-l x ⊢V⦂ A) → (H : Fam D (Γ₀ ᴱ)) → (op : Op) → (ε : E)
       → (e : (Γ₀ ᴱ ++ᶜ Dcl D op ε)
            ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε)))
       → IsSub (sub-atᶜ {split-l x ᴱ} {A} (split-r x ᴱ ++ᶜ Dcl D op ε)
                        (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) e (H op ε))
                        (eternal-val-restrict et W))
               (⟨ yes et ⟩[ x ↦ W ]cl H op ε)
cl-yes et x W H op ε e =
  isSub-reassoc (cl-yes-raw et x W H op ε) (cl-yes-sub et x W H op ε e)

-- The equation `cl-yes` wants is the splitting's own.

eCl : ∀ {Γ₀ A ρ} → (et : Eternal A) → (x : A ∈[ ρ ] Γ₀) → (D : VType)
    → (op : Op) → (ε : E)
    → (Γ₀ ᴱ ++ᶜ Dcl D op ε)
    ≡ ((split-l x ᴱ ∷ A) ++ᶜ (split-r x ᴱ ++ᶜ Dcl D op ε))
eCl et x D op ε =
  sym (split-≡ (split-++ʳ (∈-ᴱ-split et x) (Dcl D op ε)))

-- ONE ENTRY ETERNAL
--
-- Exactly one side of each order substitutes, and both substitute the
-- same restricted value — but `cl-yes` lands them at contexts that agree
-- only propositionally (`split-r (bvar B₁ Θ) ≡ Θ` against
-- `split-r (bvar B₁ (([] ∷ B₂) ++ᶜ Θ)) ≡ ([] ∷ B₂) ++ᶜ Θ`, whose eternal
-- parts coincide because `B₂` is not eternal). `sub-at-IsSub` aligns
-- them; everything else is transports.

cl-swap-en : ∀ {Γ B₁ B₂ D} → (et₁ : Eternal B₁) → (¬et₂ : ¬ Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε

cl-swap-en {Γ} {B₁} {B₂} {D} et₁ ¬et₂ Θ H W₂ W₁ op ε =
  ≡→≐ᶜ (isSub-uniq lhs rhs)
  where
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    xL = bvar {Γ} B₁ Θ
    xR = bvar {Γ} B₁ (Δ₂ ++ᶜ Θ)

    K : Fam D (((Γ ∷ B₁) ++ᶜ Θ) ᴱ)
    K = sub-atᴴ′ (no ¬et₂) Θ H Ŵ₂

    H' : Fam D (((Γ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ)) ᴱ)
    H' op' ε' = Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')

    eL = eCl et₁ xL D op ε
    eR = eCl et₁ xR D op ε

    -- both substituted terms are transports of the clause
    isL : IsSub (H op ε) (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
    isL =
      isSub-substC _ eL
        (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
          (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
            (isSub-refl (H op ε))))

    isR : IsSub (H op ε) (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eR (H' op ε))
    isR =
      isSub-substC _ eR
        (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ) (isSub-refl (H op ε)))

    -- and the two prefixes/suffixes agree
    eΓ : split-l xL ᴱ ≡ split-l xR ᴱ
    eΓ = cong _ᴱ (trans (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))
                        (sym (split→∈-split-l
                               (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))

    -- `B₂` is not eternal, so the extra entry disappears from the
    -- restriction and the two suffixes' eternal parts coincide
    eΘᴱ : Θ ᴱ ≡ (Δ₂ ++ᶜ Θ) ᴱ
    eΘᴱ = sym (trans (ᴱ-++ᶜ Δ₂ Θ)
                (trans (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-drop {[]} {B₂} ¬et₂))
                       (++ᶜ-identityˡ {Θ ᴱ})))

    eΘ : (split-r xL ᴱ ++ᶜ Dc) ≡ (split-r xR ᴱ ++ᶜ Dc)
    eΘ = cong (_++ᶜ Dc)
              (trans (cong _ᴱ (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Θ})))
                (trans eΘᴱ
                       (cong _ᴱ (sym (split→∈-split-r
                                       (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))))

    eV : subst (_⊢V⦂ B₁) eΓ
           (eternal-val-restrict et₁ (bval {Γ} Θ W₁))
       ≡ eternal-val-restrict et₁ (bval {Γ} (Δ₂ ++ᶜ Θ) W₁)
    eV =
      trans (cong (subst (_⊢V⦂ B₁) eΓ)
              (trans (cong (eternal-val-restrict et₁)
                           (castᵛ≡subst _ W₁))
                     (restrict-substᵛ _ et₁ W₁)))
        (trans (subst-fuseᵛ _ eΓ (eternal-val-restrict et₁ W₁))
          (trans (substᵛ-irr _ (cong _ᴱ (sym (split→∈-split-l
                                    (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))))
                             (eternal-val-restrict et₁ W₁))
            (trans (sym (restrict-substᵛ _ et₁ W₁))
                   (cong (eternal-val-restrict et₁)
                         (sym (castᵛ≡subst _ W₁))))))

    aligned : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                             (eternal-val-restrict et₁ (bval Θ W₁)))
                    (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eR (H' op ε))
                             (eternal-val-restrict et₁ (bval (Δ₂ ++ᶜ Θ) W₁)))
    aligned = sub-at-IsSub eΓ eΘ _ _ (isSub-reassoc isR isL) _ _ eV

    lhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                         (eternal-val-restrict et₁ (bval Θ W₁)))
                (outerᴴ′ (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-trans (cl-yes et₁ xL (bval Θ W₁) K op ε eL)
        (isSub-Cl op ε _ (castOf {Γ} {B₁} Θ) (isSub-refl _))

    rhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ D ‼ (op-grade op ·ₑ ε)) eL (K op ε))
                         (eternal-val-restrict et₁ (bval Θ W₁)))
                (innerᴴ′ (yes et₁) (no ¬et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-trans aligned
        (isSub-trans (cl-yes et₁ xR (bval (Δ₂ ++ᶜ Θ) W₁) H' op ε eR)
          (isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₂ (bvar B₂ Θ))
              (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
                (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
                          (isSub-refl _))))))

-- THE VALUE BRIDGE THE TWO REMAINING BRANCHES NEED
--
-- Where the left order weakens the outer value past `B₁` before
-- restricting it and the right order does not, the two agree — at a
-- *non-eternal* `B₁` the restriction of the weakening is the identity
-- (`ren-ᴱ-∷′ B₁ (no ¬et₁)` is `id-ren`), so this is
-- `eternal-val-restrict-ren` followed by `V-rename-id-≐`. Stated against
-- an arbitrary proof of the (only propositional) context equation, so the
-- caller may present it with whichever proof it has; `rewrite` then
-- reduces both `_ᴱ` and `ᴱ-∷-drop`, and `uip` finishes.

-- renaming along an identity-like renaming is the transport (the value
-- counterpart of `C-rename-eq-≐`)

V-rename-eq-≐ : ∀ {Γ Γ' A} → (e : Γ ≡ Γ') → {r : Ren [] Γ Γ'}
              → r ≐ʳ eq-ren e → (V : Γ ⊢V⦂ A)
              → V-rename r V ≐ᵛ subst (_⊢V⦂ A) e V
V-rename-eq-≐ refl h V = V-rename-id-≐ h V

restrict-wk-ne-≐ : ∀ {Γ₀ A B} → (¬et : ¬ Eternal B) → (et : Eternal A)
                 → (V : Γ₀ ⊢V⦂ A) → (e : Γ₀ ᴱ ≡ (Γ₀ ∷ B) ᴱ)
                 → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                 ≐ᵛ subst (_⊢V⦂ A) e (eternal-val-restrict et V)
restrict-wk-ne-≐ {Γ₀} {A} {B} ¬et et V e =
  ≐ᵛ-trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
           (V-rename-eq-≐ e (restrict-wk-≐ ¬et [] e) (eternal-val-restrict et V))

-- and the action respects `_≐ᵛ_` in the value it substitutes

sub-atᶜ-≐ᵥ : ∀ {Γ' B C} → (Θ : Ctx) → (X : ((Γ' ∷ B) ++ᶜ Θ) ⊢C⦂ C)
           → {V V' : Γ' ⊢V⦂ B} → V ≐ᵛ V'
           → sub-atᶜ Θ X V ≐ᶜ sub-atᶜ Θ X V'
sub-atᶜ-≐ᵥ Θ X eV = castᶜ-≐ _ (sub-≐ᶜ _ (castᵛ-≐ _ eV) (≐ᶜ-refl X))

-- two transports of `≐ᶜ`-related terms are `≐ᶜ`-related

isSub-≐ : ∀ {Γ₀ Γ₁ C} → {M M' : Γ₀ ⊢C⦂ C} → {X Y : Γ₁ ⊢C⦂ C}
        → IsSub M X → IsSub M' Y → M ≐ᶜ M' → X ≐ᶜ Y
isSub-≐ {C = C} {M' = M'} (e , q) (e' , q') eM =
  ≐ᶜ-trans (≡→≐ᶜ q)
    (≐ᶜ-trans (substᶜ-≐ e eM)
      (≡→≐ᶜ (trans (cong (λ z → subst (_⊢C⦂ C) z M') (uip {p = e} {q = e'}))
                   (sym q'))))

-- THE OUTER ENTRY ETERNAL, THE INNER ONE NOT
--
-- As `cl-swap-en`, except that here the two substituted values differ: the
-- left order restricts `W₂` *weakened past `B₁`*, the right order restricts
-- `W₂` itself. `restrict-wk-ne-≐` bridges them — at a non-eternal `B₁` the
-- restriction of that weakening is the identity — so the two `sub-atᶜ`s
-- agree only up to `_≐ᵛ_`, and the branch is `≐ᶜ` rather than `≡`.

cl-swap-ne : ∀ {Γ B₁ B₂ D} → (¬et₁ : ¬ Eternal B₁) → (et₂ : Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε

cl-swap-ne {Γ} {B₁} {B₂} {D} ¬et₁ et₂ Θ H W₂ W₁ op ε =
  isSub-≐ lhs' rhs valStep
  where
    CT = D ‼ (op-grade op ·ₑ ε)
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    xL = bvar {Γ ∷ B₁} B₂ Θ
    xR = bvar {Γ} B₂ Θ

    G : Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
    G = inner₀ᴴ′ (no ¬et₁) Θ H W₁

    eL = eCl et₂ xL D op ε
    eR = eCl et₂ xR D op ε

    VL = eternal-val-restrict et₂ (bval {Γ ∷ B₁} Θ Ŵ₂)
    VR = eternal-val-restrict et₂ (bval {Γ} Θ W₂)

    isL : IsSub (H op ε) (subst (_⊢C⦂ CT) eL (H op ε))
    isL = isSub-substC _ eL (isSub-refl (H op ε))

    isR : IsSub (H op ε) (subst (_⊢C⦂ CT) eR (G op ε))
    isR =
      isSub-substC _ eR
        (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
          (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
            (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ (Δ₂ ++ᶜ Θ)))
              (isSub-Cl op ε _ (assocᴮ Γ B₁ B₂ Θ) (isSub-refl (H op ε))))))

    -- `B₁` is not eternal, so the two prefixes' eternal parts coincide
    eΓ : split-l xL ᴱ ≡ split-l xR ᴱ
    eΓ = trans (cong _ᴱ (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ})))
           (trans (ᴱ-∷-drop {Γ} {B₁} ¬et₁)
                  (cong _ᴱ (sym (split→∈-split-l
                                  (split-≡-++ᶜ {Γ ∷ B₂} {Θ})))))

    eΘ : (split-r xL ᴱ ++ᶜ Dc) ≡ (split-r xR ᴱ ++ᶜ Dc)
    eΘ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
              (trans (split→∈-split-r (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))
                     (sym (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))))

    aligned : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ CT) eL (H op ε)) VL)
                    (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                             (subst (_⊢C⦂ CT) eR (G op ε))
                             (subst (_⊢V⦂ B₂) eΓ VL))
    aligned = sub-at-IsSub eΓ eΘ _ _ (isSub-reassoc isR isL) VL _ refl

    lhs : IsSub (sub-atᶜ (split-r xL ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ CT) eL (H op ε)) VL)
                (outerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lhs =
      isSub-trans (cl-yes et₂ xL (bval Θ Ŵ₂) H op ε eL)
        (isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
          (isSub-substD Dc _ (ᴱ-drop-split ¬et₁ (bvar B₁ Θ))
            (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ) (isSub-refl _))))

    rhs : IsSub (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                         (subst (_⊢C⦂ CT) eR (G op ε)) VR)
                (innerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    rhs =
      isSub-trans (cl-yes et₂ xR (bval Θ W₂) G op ε eR)
        (isSub-Cl op ε _ (castOf {Γ} {B₂} Θ) (isSub-refl _))

    cL : (Γ ∷ B₁) ≡ split-l xL
    cL = sym (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    cR : Γ ≡ split-l xR
    cR = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    e₀ : Γ ᴱ ≡ (Γ ∷ B₁) ᴱ
    e₀ = sym (ᴱ-∷-drop {Γ} {B₁} ¬et₁)

    eVal : subst (_⊢V⦂ B₂) eΓ VL ≐ᵛ VR
    eVal =
      ≐ᵛ-trans
        (≡→≐ᵛ (cong (subst (_⊢V⦂ B₂) eΓ)
                (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cL Ŵ₂))
                       (restrict-substᵛ cL et₂ Ŵ₂))))
        (≐ᵛ-trans
          (substᵛ-≐ eΓ (substᵛ-≐ (cong _ᴱ cL)
                                 (restrict-wk-ne-≐ ¬et₁ et₂ W₂ e₀)))
          (≡→≐ᵛ
            (trans (cong (subst (_⊢V⦂ B₂) eΓ)
                     (subst-fuseᵛ e₀ (cong _ᴱ cL)
                                  (eternal-val-restrict et₂ W₂)))
              (trans (subst-fuseᵛ (trans e₀ (cong _ᴱ cL)) eΓ
                                  (eternal-val-restrict et₂ W₂))
                (trans (substᵛ-irr (trans (trans e₀ (cong _ᴱ cL)) eΓ)
                                   (cong _ᴱ cR)
                                   (eternal-val-restrict et₂ W₂))
                  (trans (sym (restrict-substᵛ cR et₂ W₂))
                         (cong (eternal-val-restrict et₂)
                               (sym (castᵛ≡subst cR W₂)))))))))

    valStep : sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR (G op ε))
                      (subst (_⊢V⦂ B₂) eΓ VL)
            ≐ᶜ sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                       (subst (_⊢C⦂ CT) eR (G op ε)) VR
    valStep = sub-atᶜ-≐ᵥ _ _ eVal

    lhs' : IsSub (sub-atᶜ (split-r xR ᴱ ++ᶜ Dc)
                          (subst (_⊢C⦂ CT) eR (G op ε))
                          (subst (_⊢V⦂ B₂) eΓ VL))
                 (outerᴴ′ (no ¬et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lhs' = isSub-reassoc lhs aligned

-- The eternal counterpart of `restrict-wk-ne-≐`: at an *eternal* `B` the
-- restriction of the weakening is the weakening again, so restricting a
-- `B`-weakened value is weakening its restriction — which is exactly the
-- value `outerᶜ` hands its inner step.

restrict-wk-et-≐ᵛ : ∀ {Γ₀ A B} → (etB : Eternal B) → (et : Eternal A)
                  → (V : Γ₀ ⊢V⦂ A) → (e : (Γ₀ ∷ B) ᴱ ≡ Γ₀ ᴱ ∷ B)
                  → eternal-val-restrict et (V-rename (wk-ren {A = B}) V)
                  ≐ᵛ subst (_⊢V⦂ A) (sym e)
                       (V-rename (wk-ren {A = B}) (eternal-val-restrict et V))
restrict-wk-et-≐ᵛ {Γ₀} {A} {B} etB et V e =
  ≐ᵛ-trans (eternal-val-restrict-ren et (wk-ren {A = B}) V)
    (≐ᵛ-trans (V-rename-≐ (restrict-wk-et-≐ etB [] refl e)
                          (eternal-val-restrict et V))
      (≐ᵛ-trans (V-rename-∘ (eq-ren (sym e)) (wk-ren ∘ʳ eq-ren refl)
                            (eternal-val-restrict et V))
        (≐ᵛ-trans
          (V-rename-cong (eq-ren (sym e))
            (≐ᵛ-trans (V-rename-∘ (wk-ren {A = B}) (eq-ren refl)
                                  (eternal-val-restrict et V))
                      (V-rename-cong (wk-ren {A = B})
                                     (V-rename-id-≐ ≐ʳ-refl _))))
          (V-rename-eq-≐ (sym e) ≐ʳ-refl _))))

-- The `_≐ᶜ_`-flavoured alignment the both-eternal branch needs. Unlike
-- `sub-at-IsSub` it takes the terms related only up to `_≐ᶜ_` and the
-- values only up to `_≐ᵛ_` — which is what the nested case forces, the
-- inner `sub-atᶜ`s' values being restrictions of *weakened* values, equal
-- to the unweakened ones only up to `restrict-wk-et-≐ᵛ`.

sub-at-≐ : ∀ {Γ₁ Γ₂ B C Θ₁ Θ₂} → (eΓ : Γ₁ ≡ Γ₂) → (eΘ : Θ₁ ≡ Θ₂)
         → (X₁ : ((Γ₁ ∷ B) ++ᶜ Θ₁) ⊢C⦂ C) → (X₂ : ((Γ₂ ∷ B) ++ᶜ Θ₂) ⊢C⦂ C)
         → (e : ((Γ₁ ∷ B) ++ᶜ Θ₁) ≡ ((Γ₂ ∷ B) ++ᶜ Θ₂))
         → X₂ ≐ᶜ subst (_⊢C⦂ C) e X₁
         → (V₁ : Γ₁ ⊢V⦂ B) → (V₂ : Γ₂ ⊢V⦂ B)
         → subst (_⊢V⦂ B) eΓ V₁ ≐ᵛ V₂
         → (e' : (Γ₁ ++ᶜ Θ₁) ≡ (Γ₂ ++ᶜ Θ₂))
         → sub-atᶜ Θ₂ X₂ V₂ ≐ᶜ subst (_⊢C⦂ C) e' (sub-atᶜ Θ₁ X₁ V₁)
sub-at-≐ {C = C} refl refl X₁ X₂ e eX V₁ V₂ eV e'
  rewrite uip {p = e} {q = refl} | uip {p = e'} {q = refl} =
  ≐ᶜ-trans (sub-atᶜ-≐ _ V₂ eX) (sub-atᶜ-≐ᵥ _ X₁ (≐ᵛ-sym eV))

-- The recursion the both-eternal branch makes, with its context given by
-- an equation rather than literally — as `sub-wk-C-cast`, and for the same
-- reason: casting the clause into shape is not structurally smaller, so the
-- termination checker would reject it. Forward-declared here and defined
-- after the induction, which puts it in the same recursive group; the
-- decrease is the clause `H op ε` against the `handle` node.

sub-swap-C-cast : ∀ {Γ B₁ B₂ Γ₀ C} → (Θ : Ctx)
                → (e : Γ₀ ≡ ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ))
                → (M : Γ₀ ⊢C⦂ C) → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → SubSwapC Θ (subst (_⊢C⦂ C) e M) W₂ W₁

-- BOTH ENTRIES ETERNAL
--
-- Both orders substitute twice, so after `cl-yes` on all four
-- substitutions the two sides *are* `outerᶜ` and `innerᶜ` at the
-- restricted contexts — at an eternal `B₁`, `(Γ ∷ B₁) ᴱ` is `Γ ᴱ ∷ B₁`,
-- and at an eternal `B₂` the right order's inner suffix is
-- `([] ∷ B₂) ++ᶜ Θ ᴱ ++ᶜ Dcl`, which is `inner₀ᶜ`'s own re-bracketing up
-- to one `++ᶜ-assoc`. So the branch is `sub-swap-C` at `Θ ᴱ ++ᶜ Dcl`, and
-- the rest is the nested alignment: `sub-at-≐` at the inner level, then
-- again at the outer, on each side.

cl-swap-ee : ∀ {Γ B₁ B₂ D} → (et₁ : Eternal B₁) → (et₂ : Eternal B₂)
           → (Θ : Ctx) → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁) → (op : Op) → (ε : E)
           → ClSwap (yes et₁) (yes et₂) Θ H W₂ W₁ op ε

cl-swap-ee {Γ} {B₁} {B₂} {D} et₁ et₂ Θ H W₂ W₁ op ε =
  ≐ᶜ-trans ee-left
    (≐ᶜ-trans (substᶜ-≐ eLfin (sub-swap-C-cast Θ' eXfull (H op ε) V₂ᴱ V₁ᴱ))
      (≐ᶜ-trans (≡→≐ᶜ (cong (λ z → subst (_⊢C⦂ CT) z (innerᶜ Θ' X V₂ᴱ V₁ᴱ))
                            (uip {p = eLfin} {q = eRfin})))
                (≐ᶜ-sym ee-right)))
  where
    CT = D ‼ (op-grade op ·ₑ ε)
    Dc = Dcl D op ε
    Δ₂ = [] ∷ B₂
    Θ' = Θ ᴱ ++ᶜ Dc
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂

    V₁ᴱ = eternal-val-restrict et₁ W₁
    V₂ᴱ = eternal-val-restrict et₂ W₂

    -- the restriction of the doubly-extended context
    eᴱ : (Γ ∷ B₁ ∷ B₂) ᴱ ≡ Γ ᴱ ∷ B₁ ∷ B₂
    eᴱ = trans (ᴱ-∷-keep {Γ ∷ B₁} {B₂} et₂)
               (cong (_∷ B₂) (ᴱ-∷-keep {Γ} {B₁} et₁))

    eXfull : (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ ++ᶜ Dc) ≡ ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ')
    eXfull =
      trans (cong (_++ᶜ Dc)
              (trans (ᴱ-++ᶜ (Γ ∷ B₁ ∷ B₂) Θ) (cong (_++ᶜ Θ ᴱ) eᴱ)))
            (++ᶜ-assoc (Γ ᴱ ∷ B₁ ∷ B₂) (Θ ᴱ) Dc)

    X : ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ') ⊢C⦂ CT
    X = subst (_⊢C⦂ CT) eXfull (H op ε)

    ----------------------------------------------------------------
    -- the left order
    ----------------------------------------------------------------

    xL₁ = bvar {Γ} B₁ Θ
    xL₂ = bvar {Γ ∷ B₁} B₂ Θ

    K : Fam D (((Γ ∷ B₁) ++ᶜ Θ) ᴱ)
    K = sub-atᴴ′ (yes et₂) Θ H Ŵ₂

    eL₂ = eCl et₂ xL₂ D op ε
    eL₁ = eCl et₁ xL₁ D op ε

    VL₂ = eternal-val-restrict et₂ (bval {Γ ∷ B₁} Θ Ŵ₂)
    VL₁ = eternal-val-restrict et₁ (bval {Γ} Θ W₁)

    subatL₂ = sub-atᶜ {split-l xL₂ ᴱ} {B₂} (split-r xL₂ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eL₂ (H op ε)) VL₂
    subatL₁ = sub-atᶜ {split-l xL₁ ᴱ} {B₁} (split-r xL₁ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eL₁ (K op ε)) VL₁

    cL₂ : (Γ ∷ B₁) ≡ split-l xL₂
    cL₂ = sym (split→∈-split-l (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    cL₁ : Γ ≡ split-l xL₁
    cL₁ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))

    eΓL₂ : split-l xL₂ ᴱ ≡ Γ ᴱ ∷ B₁
    eΓL₂ = trans (cong _ᴱ (sym cL₂)) (ᴱ-∷-keep {Γ} {B₁} et₁)

    eΘL₂ : (split-r xL₂ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘL₂ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {(Γ ∷ B₁) ∷ B₂} {Θ}))

    eΓL₁ : split-l xL₁ ᴱ ≡ Γ ᴱ
    eΓL₁ = cong _ᴱ (sym cL₁)

    eΘL₁ : (split-r xL₁ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘL₁ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Θ}))

    valL₂ : subst (_⊢V⦂ B₂) eΓL₂ VL₂ ≐ᵛ V-rename (wk-ren {A = B₁}) V₂ᴱ
    valL₂ =
      ≐ᵛ-trans
        (≡→≐ᵛ (cong (subst (_⊢V⦂ B₂) eΓL₂)
                (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cL₂ Ŵ₂))
                       (restrict-substᵛ cL₂ et₂ Ŵ₂))))
        (≐ᵛ-trans
          (substᵛ-≐ eΓL₂
            (substᵛ-≐ (cong _ᴱ cL₂)
              (restrict-wk-et-≐ᵛ et₁ et₂ W₂ (ᴱ-∷-keep {Γ} {B₁} et₁))))
          (≡→≐ᵛ
            (trans (cong (subst (_⊢V⦂ B₂) eΓL₂)
                     (subst-fuseᵛ (sym (ᴱ-∷-keep {Γ} {B₁} et₁)) (cong _ᴱ cL₂)
                                  (V-rename (wk-ren {A = B₁}) V₂ᴱ)))
              (trans (subst-fuseᵛ _ eΓL₂ (V-rename (wk-ren {A = B₁}) V₂ᴱ))
                     (substᵛ-irr _ refl (V-rename (wk-ren {A = B₁}) V₂ᴱ))))))

    valL₁ : subst (_⊢V⦂ B₁) eΓL₁ VL₁ ≐ᵛ V₁ᴱ
    valL₁ =
      ≡→≐ᵛ
        (trans (cong (subst (_⊢V⦂ B₁) eΓL₁)
                 (trans (cong (eternal-val-restrict et₁) (castᵛ≡subst cL₁ W₁))
                        (restrict-substᵛ cL₁ et₁ W₁)))
          (trans (subst-fuseᵛ (cong _ᴱ cL₁) eΓL₁ V₁ᴱ)
                 (substᵛ-irr _ refl V₁ᴱ)))

    -- the inner alignment
    Oᴵ = sub-atᶜ {Γ ᴱ ∷ B₁} {B₂} Θ' X (V-rename (wk-ren {A = B₁}) V₂ᴱ)

    eIL : ((split-l xL₂ ᴱ ∷ B₂) ++ᶜ (split-r xL₂ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁ ∷ B₂) ++ᶜ Θ')
    eIL = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₂) ++ᶜ Θ₀) eΓL₂ eΘL₂

    eIL' : (split-l xL₂ ᴱ ++ᶜ (split-r xL₂ ᴱ ++ᶜ Dc)) ≡ ((Γ ᴱ ∷ B₁) ++ᶜ Θ')
    eIL' = cong₂ _++ᶜ_ eΓL₂ eΘL₂

    oI : Oᴵ ≐ᶜ subst (_⊢C⦂ CT) eIL' subatL₂
    oI =
      sub-at-≐ eΓL₂ eΘL₂ (subst (_⊢C⦂ CT) eL₂ (H op ε)) X eIL
        (≡→≐ᶜ (sym (trans (subst-fuseᶜ eL₂ eIL (H op ε))
                          (cong (λ z → subst (_⊢C⦂ CT) z (H op ε))
                                (uip {p = trans eL₂ eIL} {q = eXfull})))))
        VL₂ (V-rename (wk-ren {A = B₁}) V₂ᴱ) valL₂ eIL'

    kIs : IsSub subatL₂ (subst (_⊢C⦂ CT) eL₁ (K op ε))
    kIs =
      isSub-substC _ eL₁
        (isSub-Cl op ε _ (castOf {Γ ∷ B₁} {B₂} Θ)
          (cl-yes et₂ xL₂ (bval Θ Ŵ₂) H op ε eL₂))

    eOL : ((split-l xL₁ ᴱ ∷ B₁) ++ᶜ (split-r xL₁ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁) ++ᶜ Θ')
    eOL = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₁) ++ᶜ Θ₀) eΓL₁ eΘL₁

    eOL' : (split-l xL₁ ᴱ ++ᶜ (split-r xL₁ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ Θ')
    eOL' = cong₂ _++ᶜ_ eΓL₁ eΘL₁

    termO : Oᴵ ≐ᶜ subst (_⊢C⦂ CT) eOL (subst (_⊢C⦂ CT) eL₁ (K op ε))
    termO =
      ≐ᶜ-trans oI
        (≡→≐ᶜ
          (trans (cong (λ z → subst (_⊢C⦂ CT) z subatL₂)
                       (uip {p = eIL'} {q = trans (proj₁ kIs) eOL}))
            (trans (sym (subst-fuseᶜ (proj₁ kIs) eOL subatL₂))
                   (cong (subst (_⊢C⦂ CT) eOL) (sym (proj₂ kIs))))))

    oO : outerᶜ Θ' X V₂ᴱ V₁ᴱ ≐ᶜ subst (_⊢C⦂ CT) eOL' subatL₁
    oO =
      sub-at-≐ eΓL₁ eΘL₁ (subst (_⊢C⦂ CT) eL₁ (K op ε)) Oᴵ eOL termO
               VL₁ V₁ᴱ valL₁ eOL'

    lIs : IsSub subatL₁ (outerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε)
    lIs =
      isSub-Cl op ε _ (castOf {Γ} {B₁} Θ)
        (cl-yes et₁ xL₁ (bval Θ W₁) K op ε eL₁)

    eLfin : (Γ ᴱ ++ᶜ Θ') ≡ (((Γ ++ᶜ Θ) ᴱ) ++ᶜ Dc)
    eLfin = trans (sym eOL') (proj₁ lIs)

    ee-left : outerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε
            ≐ᶜ subst (_⊢C⦂ CT) eLfin (outerᶜ Θ' X V₂ᴱ V₁ᴱ)
    ee-left =
      ≐ᶜ-trans (≡→≐ᶜ (proj₂ lIs))
        (≐ᶜ-sym
          (≐ᶜ-trans (substᶜ-≐ eLfin oO)
            (≡→≐ᶜ (trans (subst-fuseᶜ eOL' eLfin subatL₁)
                         (cong (λ z → subst (_⊢C⦂ CT) z subatL₁) uip)))))

    ----------------------------------------------------------------
    -- the right order
    ----------------------------------------------------------------

    xR₂ = bvar {Γ} B₂ Θ
    xR₁ = bvar {Γ} B₁ (Δ₂ ++ᶜ Θ)

    H' : Fam D (((Γ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ)) ᴱ)
    H' op' ε' = Cl-cast op' ε' (assocᴮ Γ B₁ B₂ Θ) (H op' ε')

    G : Fam D (((Γ ∷ B₂) ++ᶜ Θ) ᴱ)
    G = inner₀ᴴ′ (yes et₁) Θ H W₁

    eR₁ = eCl et₁ xR₁ D op ε
    eR₂ = eCl et₂ xR₂ D op ε

    VR₁ = eternal-val-restrict et₁ (bval {Γ} (Δ₂ ++ᶜ Θ) W₁)
    VR₂ = eternal-val-restrict et₂ (bval {Γ} Θ W₂)

    subatR₁ = sub-atᶜ {split-l xR₁ ᴱ} {B₁} (split-r xR₁ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR₁ (H' op ε)) VR₁
    subatR₂ = sub-atᶜ {split-l xR₂ ᴱ} {B₂} (split-r xR₂ ᴱ ++ᶜ Dc)
                      (subst (_⊢C⦂ CT) eR₂ (G op ε)) VR₂

    cR₁ : Γ ≡ split-l xR₁
    cR₁ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ}))

    cR₂ : Γ ≡ split-l xR₂
    cR₂ = sym (split→∈-split-l (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    eΓR₁ : split-l xR₁ ᴱ ≡ Γ ᴱ
    eΓR₁ = cong _ᴱ (sym cR₁)

    eΓR₂ : split-l xR₂ ᴱ ≡ Γ ᴱ
    eΓR₂ = cong _ᴱ (sym cR₂)

    -- at an eternal `B₂` the extra entry survives the restriction, and
    -- one `++ᶜ-assoc` turns it into `inner₀ᶜ`'s own bracketing
    eΘR₁ : (split-r xR₁ ᴱ ++ᶜ Dc) ≡ (Δ₂ ++ᶜ Θ')
    eΘR₁ =
      trans (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                  (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₁} {Δ₂ ++ᶜ Θ})))
        (trans (cong (_++ᶜ Dc)
                 (trans (ᴱ-++ᶜ Δ₂ Θ)
                        (cong (_++ᶜ Θ ᴱ) (ᴱ-∷-keep {[]} {B₂} et₂))))
               (++ᶜ-assoc Δ₂ (Θ ᴱ) Dc))

    eΘR₂ : (split-r xR₂ ᴱ ++ᶜ Dc) ≡ Θ'
    eΘR₂ = cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                (split→∈-split-r (split-≡-++ᶜ {Γ ∷ B₂} {Θ}))

    valR₁ : subst (_⊢V⦂ B₁) eΓR₁ VR₁ ≐ᵛ V₁ᴱ
    valR₁ =
      ≡→≐ᵛ
        (trans (cong (subst (_⊢V⦂ B₁) eΓR₁)
                 (trans (cong (eternal-val-restrict et₁) (castᵛ≡subst cR₁ W₁))
                        (restrict-substᵛ cR₁ et₁ W₁)))
          (trans (subst-fuseᵛ (cong _ᴱ cR₁) eΓR₁ V₁ᴱ)
                 (substᵛ-irr _ refl V₁ᴱ)))

    valR₂ : subst (_⊢V⦂ B₂) eΓR₂ VR₂ ≐ᵛ V₂ᴱ
    valR₂ =
      ≡→≐ᵛ
        (trans (cong (subst (_⊢V⦂ B₂) eΓR₂)
                 (trans (cong (eternal-val-restrict et₂) (castᵛ≡subst cR₂ W₂))
                        (restrict-substᵛ cR₂ et₂ W₂)))
          (trans (subst-fuseᵛ (cong _ᴱ cR₂) eΓR₂ V₂ᴱ)
                 (substᵛ-irr _ refl V₂ᴱ)))

    Iᴵ = sub-atᶜ {Γ ᴱ} {B₁} (Δ₂ ++ᶜ Θ')
                 (castᶜ (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X) V₁ᴱ

    eIR : ((split-l xR₁ ᴱ ∷ B₁) ++ᶜ (split-r xR₁ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₁) ++ᶜ (Δ₂ ++ᶜ Θ'))
    eIR = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₁) ++ᶜ Θ₀) eΓR₁ eΘR₁

    eIR' : (split-l xR₁ ᴱ ++ᶜ (split-r xR₁ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ (Δ₂ ++ᶜ Θ'))
    eIR' = cong₂ _++ᶜ_ eΓR₁ eΘR₁

    iI : Iᴵ ≐ᶜ subst (_⊢C⦂ CT) eIR' subatR₁
    iI =
      sub-at-≐ eΓR₁ eΘR₁ (subst (_⊢C⦂ CT) eR₁ (H' op ε))
               (castᶜ (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X) eIR
        (≡→≐ᶜ
          (trans (castᶜ≡subst (assocᴮ (Γ ᴱ) B₁ B₂ Θ') X)
            (trans (subst-fuseᶜ eXfull (assocᴮ (Γ ᴱ) B₁ B₂ Θ') (H op ε))
              (trans (cong (λ z → subst (_⊢C⦂ CT) z (H op ε))
                           (uip {q = trans (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                                                 (assocᴮ Γ B₁ B₂ Θ))
                                           (trans eR₁ eIR)}))
                (trans (sym (subst-fuseᶜ (cong (λ Γ₀ → Γ₀ ᴱ ++ᶜ Dc)
                                               (assocᴮ Γ B₁ B₂ Θ))
                                         (trans eR₁ eIR) (H op ε)))
                  (trans (cong (subst (_⊢C⦂ CT) (trans eR₁ eIR))
                               (sym (castᶜ≡subst _ (H op ε))))
                         (sym (subst-fuseᶜ eR₁ eIR (H' op ε)))))))))
        VR₁ V₁ᴱ valR₁ eIR'

    gIs : IsSub subatR₁ (subst (_⊢C⦂ CT) eR₂ (G op ε))
    gIs =
      isSub-substC _ eR₂
        (isSub-Cl op ε _ (assocᴮ⁻ Γ B₂ Θ)
          (isSub-Cl op ε _ (castOf {Γ} {B₁} (Δ₂ ++ᶜ Θ))
            (cl-yes et₁ xR₁ (bval (Δ₂ ++ᶜ Θ) W₁) H' op ε eR₁)))

    eOR : ((split-l xR₂ ᴱ ∷ B₂) ++ᶜ (split-r xR₂ ᴱ ++ᶜ Dc))
        ≡ ((Γ ᴱ ∷ B₂) ++ᶜ Θ')
    eOR = cong₂ (λ Γ₀ Θ₀ → (Γ₀ ∷ B₂) ++ᶜ Θ₀) eΓR₂ eΘR₂

    eOR' : (split-l xR₂ ᴱ ++ᶜ (split-r xR₂ ᴱ ++ᶜ Dc)) ≡ (Γ ᴱ ++ᶜ Θ')
    eOR' = cong₂ _++ᶜ_ eΓR₂ eΘR₂

    termOR : castᶜ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ
           ≐ᶜ subst (_⊢C⦂ CT) eOR (subst (_⊢C⦂ CT) eR₂ (G op ε))
    termOR =
      ≐ᶜ-trans (≡→≐ᶜ (castᶜ≡subst (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ))
        (≐ᶜ-trans (substᶜ-≐ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') iI)
          (≡→≐ᶜ
            (trans (subst-fuseᶜ eIR' (assocᴮ⁻ (Γ ᴱ) B₂ Θ') subatR₁)
              (trans (cong (λ z → subst (_⊢C⦂ CT) z subatR₁)
                           (uip {q = trans (proj₁ gIs) eOR}))
                (trans (sym (subst-fuseᶜ (proj₁ gIs) eOR subatR₁))
                       (cong (subst (_⊢C⦂ CT) eOR) (sym (proj₂ gIs))))))))

    iO : innerᶜ Θ' X V₂ᴱ V₁ᴱ ≐ᶜ subst (_⊢C⦂ CT) eOR' subatR₂
    iO =
      sub-at-≐ eΓR₂ eΘR₂ (subst (_⊢C⦂ CT) eR₂ (G op ε))
               (castᶜ (assocᴮ⁻ (Γ ᴱ) B₂ Θ') Iᴵ) eOR termOR
               VR₂ V₂ᴱ valR₂ eOR'

    rIs : IsSub subatR₂ (innerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε)
    rIs =
      isSub-Cl op ε _ (castOf {Γ} {B₂} Θ)
        (cl-yes et₂ xR₂ (bval Θ W₂) G op ε eR₂)

    eRfin : (Γ ᴱ ++ᶜ Θ') ≡ (((Γ ++ᶜ Θ) ᴱ) ++ᶜ Dc)
    eRfin = trans (sym eOR') (proj₁ rIs)

    ee-right : innerᴴ′ (yes et₁) (yes et₂) Θ H W₂ W₁ op ε
             ≐ᶜ subst (_⊢C⦂ CT) eRfin (innerᶜ Θ' X V₂ᴱ V₁ᴱ)
    ee-right =
      ≐ᶜ-trans (≡→≐ᶜ (proj₂ rIs))
        (≐ᶜ-sym
          (≐ᶜ-trans (substᶜ-≐ eRfin iO)
            (≡→≐ᶜ (trans (subst-fuseᶜ eOR' eRfin subatR₂)
                         (cong (λ z → subst (_⊢C⦂ CT) z subatR₂) uip)))))

-- The dispatch. `sub-atᴴ` *is* `sub-atᴴ′ (eternal? B)`, so instantiating
-- the two decisions recovers the statement on the nose.

sub-swap-clause : ∀ {Γ B₁ B₂ D} → (Θ : Ctx)
                → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → (op : Op) → (ε : E)
                → outerᴴ Θ H W₂ W₁ op ε ≐ᶜ innerᴴ Θ H W₂ W₁ op ε

sub-swap-clause {Γ} {B₁} {B₂} Θ H W₂ W₁ op ε =
  go (eternal? B₁) (eternal? B₂)
  where
    go : (dec₁ : Dec (Eternal B₁)) → (dec₂ : Dec (Eternal B₂))
       → ClSwap dec₁ dec₂ Θ H W₂ W₁ op ε
    go (no ¬et₁)  (no ¬et₂)  = cl-swap-nn ¬et₁ ¬et₂ Θ H W₂ W₁ op ε
    go (yes et₁)  (no ¬et₂)  = cl-swap-en et₁  ¬et₂ Θ H W₂ W₁ op ε
    go (no ¬et₁)  (yes et₂)  = cl-swap-ne ¬et₁ et₂  Θ H W₂ W₁ op ε
    go (yes et₁)  (yes et₂)  = cl-swap-ee et₁  et₂  Θ H W₂ W₁ op ε

sub-swap-handle : ∀ {Γ B₁ B₂ A D ε ε'} → (Θ : Ctx)
                → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ A ‼ ε)
                → (H : Fam D (((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ᴱ))
                → (N : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⟨ mapᵉ ε ⟩ ∷ A ⊢C⦂ D ‼ ε')
                → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
                → SubSwapC Θ M W₂ W₁
                → SubSwapC (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁
                → SubSwapC Θ (handle M `with H `in N) W₂ W₁

sub-swap-handle {Γ} {B₁} {B₂} {A} {ε = ε} Θ M H N W₂ W₁ ihM ihN =
  ≐ᶜ-trans
    (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁)
                       (sub-at-handle Θ M H N Ŵ₂))
                 (sub-at-handle Θ (sub-atᶜ Θ M Ŵ₂) (sub-atᴴ Θ H Ŵ₂)
                                (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N Ŵ₂) W₁)))
    (≐ᶜ-trans
      (handle-≐ ihM (λ op ε'' → sub-swap-clause Θ H W₂ W₁ op ε'') ihN)
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂)
                              (inner₀-handle Θ M H N W₁))
                        (sub-at-handle Θ (inner₀ᶜ Θ M W₁) (inner₀ᴴ Θ H W₁)
                                       (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁)
                                       W₂)))))
  where
    Ŵ₂ = V-rename (wk-ren {A = B₁}) W₂


sub-swap-V : ∀ {Γ B₁ B₂ A} → (Θ : Ctx) → (U : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢V⦂ A)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapV Θ U W₂ W₁

sub-swap-C : ∀ {Γ B₁ B₂ C} → (Θ : Ctx) → (M : ((Γ ∷ B₁ ∷ B₂) ++ᶜ Θ) ⊢C⦂ C)
           → (W₂ : Γ ⊢V⦂ B₂) → (W₁ : Γ ⊢V⦂ B₁)
           → SubSwapC Θ M W₂ W₁

sub-swap-V Θ (var f y) W₂ W₁ = sub-swap-var Θ y f W₂ W₁

sub-swap-V {Γ} {B₁} {B₂} Θ (const c) W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-const Θ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-const Θ W₁)))
           (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂)
                                   (inner₀-const Θ W₁))
                             (sub-at-const Θ W₂))))

sub-swap-V {Γ} {B₁} {B₂} Θ ⋆ W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-⋆ Θ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-⋆ Θ W₁)))
           (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂) (inner₀-⋆ Θ W₁))
                             (sub-at-⋆ Θ W₂))))

sub-swap-V {Γ} {B₁} {B₂} Θ ⦉ V₁ , V₂ ⦊ W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-pair Θ V₁ V₂ (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-pair Θ (sub-atᵛ Θ V₁ (V-rename (wk-ren {A = B₁}) W₂))
                                       (sub-atᵛ Θ V₂ (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᵛ-trans (pair-≐ (sub-swap-V Θ V₁ W₂ W₁) (sub-swap-V Θ V₂ W₂ W₁))
      (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂)
                              (inner₀-pair Θ V₁ V₂ W₁))
                        (sub-at-pair Θ (inner₀ᵛ Θ V₁ W₁)
                                       (inner₀ᵛ Θ V₂ W₁) W₂)))))

sub-swap-V {Γ} {B₁} {B₂} {A ⇒ C} Θ (lam N) W₂ W₁ =
  ≐ᵛ-trans (≡→≐ᵛ (trans (cong (λ z → sub-atᵛ Θ z W₁) (sub-at-lam Θ N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-lam Θ (sub-atᶜ (Θ ∷ A) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᵛ-trans (lam-≐ (sub-swap-C (Θ ∷ A) N W₂ W₁))
      (≡→≐ᵛ (sym (trans (cong (λ z → sub-atᵛ Θ z W₂) (inner₀-lam Θ N W₁))
                        (sub-at-lam Θ (inner₀ᶜ (Θ ∷ A) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (return V) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-ret Θ V (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-ret Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (return-≐ (sub-swap-V Θ V W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-ret Θ V W₁))
                        (sub-at-ret Θ (inner₀ᵛ Θ V W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (_⨟_ {A = A} {ε = ε} M N) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-seq Θ M N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-seq Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂))
                                      (sub-atᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (seq-≐ (sub-swap-C Θ M W₂ W₁)
                     (sub-swap-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-seq Θ M N W₁))
                        (sub-at-seq Θ (inner₀ᶜ Θ M W₁)
                                      (inner₀ᶜ (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (V · U) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-app Θ V U (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-app Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                                      (sub-atᵛ Θ U (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (app-≐ (sub-swap-V Θ V W₂ W₁) (sub-swap-V Θ U W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-app Θ V U W₁))
                        (sub-at-app Θ (inner₀ᵛ Θ V W₁)
                                      (inner₀ᵛ Θ U W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (match_`in_ {A = A₁} {B = A₂} V N) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-match Θ V N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-match Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                                        (sub-atᶜ (Θ ∷ A₁ ∷ A₂) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (match-≐ (sub-swap-V Θ V W₂ W₁)
                       (sub-swap-C (Θ ∷ A₁ ∷ A₂) N W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-match Θ V N W₁))
                        (sub-at-match Θ (inner₀ᵛ Θ V W₁)
                                        (inner₀ᶜ (Θ ∷ A₁ ∷ A₂) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (absurd V) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-absurd Θ V (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-absurd Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (absurd-≐ (sub-swap-V Θ V W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-absurd Θ V W₁))
                        (sub-at-absurd Θ (inner₀ᵛ Θ V W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (perform op V N) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-perform Θ V N (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-perform Θ (sub-atᵛ Θ V (V-rename (wk-ren {A = B₁}) W₂))
                           (sub-atᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                       ∷ type-of-gtype (arity op)) N (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (perform-≐ (sub-swap-V Θ V W₂ W₁)
                         (sub-swap-C (Θ ⟨ mapᵉ (op-grade op) ⟩
                                        ∷ type-of-gtype (arity op)) N W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂)
                              (inner₀-perform Θ V N W₁))
                        (sub-at-perform Θ (inner₀ᵛ Θ V W₁)
                           (inner₀ᶜ (Θ ⟨ mapᵉ (op-grade op) ⟩
                                       ∷ type-of-gtype (arity op)) N W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (delay τ M) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-delay Θ M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-delay Θ (sub-atᶜ (Θ ⟨ of-natʳ τ ⟩) M (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (delay-≐ (sub-swap-C (Θ ⟨ of-natʳ τ ⟩) M W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-delay Θ M W₁))
                        (sub-at-delay Θ (inner₀ᶜ (Θ ⟨ of-natʳ τ ⟩) M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (box {A = A} {ρ = ρ} V M) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁)
                              (sub-at-box Θ V M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-box Θ
                           (sub-atᵛ (Θ ⟨ ρ ⟩) V (V-rename (wk-ren {A = B₁}) W₂))
                           (sub-atᶜ (Θ ∷ [ ρ ] A) M
                                    (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (box-≐ (sub-swap-V (Θ ⟨ ρ ⟩) V W₂ W₁)
                     (sub-swap-C (Θ ∷ [ ρ ] A) M W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-box Θ V M W₁))
                        (sub-at-box Θ (inner₀ᵛ (Θ ⟨ ρ ⟩) V W₁)
                                      (inner₀ᶜ (Θ ∷ [ ρ ] A) M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (coerce p M) W₂ W₁ =
  ≐ᶜ-trans (≡→≐ᶜ (trans (cong (λ z → sub-atᶜ Θ z W₁) (sub-at-coerce Θ M (V-rename (wk-ren {A = B₁}) W₂)))
                        (sub-at-coerce Θ (sub-atᶜ Θ M (V-rename (wk-ren {A = B₁}) W₂)) W₁)))
    (≐ᶜ-trans (coerce-≐ (sub-swap-C Θ M W₂ W₁))
      (≡→≐ᶜ (sym (trans (cong (λ z → sub-atᶜ Θ z W₂) (inner₀-coerce Θ M W₁))
                        (sub-at-coerce Θ (inner₀ᶜ Θ M W₁) W₂)))))

sub-swap-C {Γ} {B₁} {B₂} Θ (handle_`with_`in {A = A} {ε = ε} M H N) W₂ W₁ =
  sub-swap-handle Θ M H N W₂ W₁
    (sub-swap-C Θ M W₂ W₁) (sub-swap-C (Θ ⟨ mapᵉ ε ⟩ ∷ A) N W₂ W₁)

sub-swap-C {Γ} {B₁} {B₂} Θ (unbox {A = A} w V M) W₂ W₁ =
  sub-swap-unbox Θ w V M W₂ W₁ (sub-swap-C (Θ ∷ A) M W₂ W₁)

sub-swap-C-cast Θ refl M W₂ W₁ = sub-swap-C Θ M W₂ W₁

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

-- Two renamings out of the empty context act alike.

empty-ren-≐ : ∀ {Γ₁} → (r r' : Ren [] [] Γ₁) → r ≐ʳ r'
empty-ren-≐ r r' = mk≐ʳ (λ x → ⊥-elim (not-in-empty-ctx x))

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
            (V-rename-≐ (empty-ren-≐ (restrict-ren (empty-ren lf))
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
    _ , castʳᵉ (++ᶜ-identityˡ {Γc}) w , V
  , unbox-tgt-castʳᵉ (++ᶜ-identityˡ {Γc}) w V
  , ≐ᶜ-trans (≡→≐ᶜ (cast-unbox (++ᶜ-identityˡ {Γc})))
      (unbox-≐ refl
        (≡→≐ᶜ (castᶜ-irr (cong (_∷ A) (++ᶜ-identityˡ {Γc}))
                         (++ᶜ-identityˡ {Γc ∷ A}) M)))

env-eternal-C-unbox {Δ ∷ B} {Γc} {A = A} (lf-∷ lf) η w V M
                    .(unbox-tgt w V) refl rel
  with env-eternal-C-unbox lf (λ x → η (Tl-∷ x))
         (castʳᵉ (castOf {Δ} {B} Γc) (unbox-var-ren (proj₂ tE) relE))
         (var (λ _ → ≾ᵣ-refl) Hd)
         (castᶜ (castOf {Δ} {B} (Γc ∷ A)) (M [ Tl-∷ (bvar B Γc) ↦ W₀ ]c))
         _
         (trans (unbox-tgt-castʳᵉ (castOf {Δ} {B} Γc)
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
         (castʳᵉ (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ)) M)
         _ (unbox-tgt-castʳᵉ (++ᶜ-assoc Γ ([] ⟨ ρ₀ ⟩) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , (cong-ren (unbox-ren q) ∘ʳ castʳᵉ eOut w₁) , V₁
  , trans (unbox-tgt-∘ (cong-ren (unbox-ren q)) (castʳᵉ eOut w₁) V₁)
          (cong (var-tgt′ (cong-ren (unbox-ren q)))
                (trans (unbox-tgt-castʳᵉ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)))
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
         (castʳᵉ (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ)) M)
         _ (unbox-tgt-castʳᵉ (++ᶜ-assoc Γ ([] ∷ [ ρ₀ ] A₀) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    Δ₁ , castʳᵉ eOut w₁ , V₁
  , trans (unbox-tgt-castʳᵉ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)
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
  with env-eternal-C-unbox lf η (castʳᵉ (++ᶜ-assoc Δ₀ Γ₁ Δ) w) V
         (castᶜ (cong (_∷ _) (++ᶜ-assoc Δ₀ Γ₁ Δ)) M)
         _ (unbox-tgt-castʳᵉ (++ᶜ-assoc Δ₀ Γ₁ Δ) w V) rel
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
         (castʳᵉ (++ᶜ-assoc Γ ([] ∷ A₀) Δ) w) V
         (castᶜ (cong (_∷ A) (++ᶜ-assoc Γ ([] ∷ A₀) Δ)) M)
         _ (unbox-tgt-castʳᵉ (++ᶜ-assoc Γ ([] ∷ A₀) Δ) w V) rel
... | Δ₁ , w₁ , V₁ , ce , eq =
    _ , castʳᵉ cOf (unbox-var-ren z relSub) , var (λ _ → ≾ᵣ-refl) Hd
  , trans (unbox-tgt-castʳᵉ cOf (unbox-var-ren z relSub)
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
          (sub-unbox (castʳᵉ eOut w₁) V₁ _ (bvar A₀ Δ) (bval Δ W) relSub)))
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

    ceOut = trans (unbox-tgt-castʳᵉ eOut w₁ V₁) (cong (Tgt-cast eOut) ce)

    relSub =
      ≾ᵣ-trans
        (proj₂ (proj₂ (⟨ proj₂ (unbox-tgt (castʳᵉ eOut w₁) V₁) ⟩[ bvar A₀ Δ
                         ↦ bval Δ W ]rvar)))
        (subst (_≾ᵣ _) (sym (cong proj₁ ceOut))
          (env-cell-rel γ ([] ∷ A₀ ++ᶜ Δ)
            (Tgt-cast (++ᶜ-assoc Γ ([] ∷ A₀) Δ) (unbox-tgt w V)) rel))

    z = proj₂ (rvar-tgt (proj₂ (unbox-tgt (castʳᵉ eOut w₁) V₁))
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
