------------------------------------------------------------------------
-- The logical relation: reducible values, computations and stores.     --
--                                                                    --
-- Unary and purely syntactic — soundness of the operational semantics  --
-- is already available and head-faithfulness is a separate model       --
-- lemma, so the relation only has to deliver weak-head normalization.   --
--                                                                    --
-- `Comp` is an *inductive family*, not a definition by recursion on the --
-- effect grade: `E` is an arbitrary preordered monoid, so                --
-- `op-grade op ·ₑ ε` need not exceed `ε`. Its induction is what carries   --
-- the `handle` case of the fundamental lemma (one `HANDLE-OP` consumes    --
-- one resumption premise). Ground types carry no arrows, so `Valᵍ` is a   --
-- prior definition and `Comp` can be given before `Val`, which then       --
-- instantiates it at the structurally smaller value predicate.            --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Reducibility (Spec : LanguageSpec) where

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

open import OperationalSemantics.Adequacy.Slice Spec

-- REDUCIBLE GROUND VALUES (recursion on `GType`)
--
-- Ground types are the parameter and arity types of operations. They contain
-- no arrows, so this needs nothing but itself — which is what lets `Comp`
-- mention it.

Valᵍ : (G : GType) → (St : 𝕊 []) → toCtx St ⊢V⦂ type-of-gtype G → Set
Valᵍ (Base b)      St V = ⊤
Valᵍ Unit          St V = ⊤
Valᵍ Empty         St V = ⊤
Valᵍ (G₁ |×|ᵍ G₂)  St V =
  Σ[ V₁ ∈ toCtx St ⊢V⦂ type-of-gtype G₁ ]
  Σ[ V₂ ∈ toCtx St ⊢V⦂ type-of-gtype G₂ ]
    (V ≡ ⦉ V₁ , V₂ ⦊) × Valᵍ G₁ St V₁ × Valᵍ G₂ St V₂
Valᵍ ([ ρ ]ᵍ G)    St V =
  ∀ {St'} → (q : Slice St ρ St' uᵣ) → Valᵍ G St' (unbox-lookup St' (unbox-ren q) V)

-- REDUCIBLE COMPUTATIONS (inductive)
--
-- `M` runs to a weak head normal form whose components are reducible. The
-- run's grade is free (a step only refines it), so the whnf's grade and state
-- are bound by the constructors; `steps-≾`/`steps-grade` recover the
-- refinement when it is needed.

data Comp (A : VType) (P : (St : 𝕊 []) → toCtx St ⊢V⦂ A → Set)
     : (ε : E) → (St : 𝕊 []) → toCtx St ⊢C⦂ A ‼ ε → Set where

  -- it returns a reducible value

  comp-ret : ∀ {ε} {St St₁ : 𝕊 []}
           → {M : toCtx St ⊢C⦂ A ‼ ε}
           → {V : toCtx St₁ ⊢V⦂ A}
           → ⟨ St , M ⟩ ↝* ⟨ St₁ , return V ⟩
           → P St₁ V
           ---------------------------------
           → Comp A P ε St M

  -- or it gets stuck on an operation with a reducible parameter, whose
  -- resumption is reducible at every later state that unboxing the
  -- continuation permits (the `Slice` at the operation's own grade)

  comp-op : ∀ {ε ε₁} {St St₁ : 𝕊 []} {op : Op}
          → {M : toCtx St ⊢C⦂ A ‼ ε}
          → {W : toCtx St₁ ⊢V⦂ type-of-gtype (param op)}
          → {M' : toCtx St₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                    ⊢C⦂ A ‼ ε₁}
          → ⟨ St , M ⟩ ↝* ⟨ St₁ , perform op W M' ⟩
          → Valᵍ (param op) St₁ W
          → (∀ {St₂ : 𝕊 []}
             → (q : Slice St₁ (mapᵉ (op-grade op)) St₂ (mapᵉ (op-grade op)))
             → (W' : toCtx (St₂ ⟨ mapᵉ (op-grade op) ⟩ₛ) ⊢V⦂ type-of-gtype (arity op))
             → Valᵍ (arity op) (St₂ ⟨ mapᵉ (op-grade op) ⟩ₛ) W'
             → Comp A P ε₁ (St₂ ⟨ mapᵉ (op-grade op) ⟩ₛ) (resume q M' W'))
          -------------------------------------------------------------------
          → Comp A P ε St M

-- REDUCIBLE VALUES (recursion on `VType`)
--
-- Over a state context a product value *is* a pair and a function value *is*
-- a lambda (`⦉⦊-not-in-toCtx`, `⇒-not-in-toCtx`), and a box-typed value is a
-- resource variable (`grad-typ⇒var`) — so only `[ ρ ]` needs a Kripke
-- quantifier, at the slice that makes the resource ready.

Val : (A : VType) → (St : 𝕊 []) → toCtx St ⊢V⦂ A → Set
Val (Base b)      St V = ⊤
Val Unit          St V = ⊤
Val Empty         St V = ⊤
Val (A |×| B)     St V =
  Σ[ V₁ ∈ toCtx St ⊢V⦂ A ] Σ[ V₂ ∈ toCtx St ⊢V⦂ B ]
    (V ≡ ⦉ V₁ , V₂ ⦊) × Val A St V₁ × Val B St V₂
Val (A ⇒ (B ‼ ε)) St V =
  Σ[ M ∈ toCtx St ∷ A ⊢C⦂ B ‼ ε ]
    (V ≡ lam M)
  × (∀ (W : toCtx St ⊢V⦂ A) → Val A St W → Comp B (Val B) ε St (M [ Hd ↦ W ]c))
Val ([ ρ ] A)     St V =
  ∀ {St'} → (q : Slice St ρ St' uᵣ) → Val A St' (unbox-lookup St' (unbox-ren q) V)

-- Reducible computations at the value predicate `Val` — the form the
-- fundamental lemma proves.

Comp' : (A : VType) → (ε : E) → (St : 𝕊 []) → toCtx St ⊢C⦂ A ‼ ε → Set
Comp' A = Comp A (Val A)

-- REDUCIBLE STORES (recursion on `𝕊`)
--
-- Every cell holds a value reducible at the stage it was allocated for. The
-- reducibility analogue of `Paramˢ`; the store is the closing environment for
-- the resource variables of `toCtx St`.

Store : 𝕊 [] → Set
Store ∅                  = ⊤
Store (St ⟨ ρ ⟩ₛ)         = Store St
Store (_∷ₛ_ {A} {ρ} St V) =
  Store St × Val A (St ⟨ ρ ⟩ₛ) (V-rename (eq-ren ++ᶜ-identityˡ) V)

-- HEAD EXPANSION
--
-- A step in front of a reducible computation: the whnf it reaches is the same
-- one, reached by the longer run. The grade changes across the step, which is
-- why `Comp` carries runs rather than a fixed grade — `_◅_` leaves it free.

Comp-expand : ∀ {A P ε ε'} {St St' : 𝕊 []}
            → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
            → ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩
            → Comp A P ε' St' M'
            -------------------------
            → Comp A P ε St M

Comp-expand r (comp-ret rs pV)   = comp-ret (r ◅ rs) pV
Comp-expand r (comp-op rs pW pk) = comp-op (r ◅ rs) pW pk

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- Ground reducibility is value reducibility at the embedded type. Needed
  -- wherever the two meet: `perform`, and the `handle` clause's parameter and
  -- resumption.

  Valᵍ→Val : ∀ {G St} → (V : toCtx St ⊢V⦂ type-of-gtype G)
           → Valᵍ G St V → Val (type-of-gtype G) St V

  Val→Valᵍ : ∀ {G St} → (V : toCtx St ⊢V⦂ type-of-gtype G)
           → Val (type-of-gtype G) St V → Valᵍ G St V

  -- Monotonicity along the slice. Only stated where it holds: a plain value
  -- moves at the unit lock (knot 1 of `notes/adequacy-plan.md` — the general
  -- `≤ₛ` reindexing is *not* available).

  Val-slice : ∀ {A St St'} → (q : Slice St uᵣ St' uᵣ) → (V : toCtx St ⊢V⦂ A)
            → Val A St V → Val A St' (slice-val q V)

  Comp-slice : ∀ {A ε St St'} → (q : Slice St uᵣ St' uᵣ) → (M : toCtx St ⊢C⦂ A ‼ ε)
             → Comp' A ε St M → Comp' A ε St' (slice-comp q M)

  -- The store makes every resource variable reducible: this is what discharges
  -- `Val`'s `[ ρ ]` clause in the variable case of the fundamental lemma.

  store-var : ∀ {A ρ ρ'} {St : 𝕊 []}
            → Store St
            → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
            → (f : ¬ Eternal ([ ρ ] A) → ρ' ≾ᵣ uᵣ)
            → Val ([ ρ ] A) St (var f x)

  -- Allocation extends a reducible store with a reducible value (`BOX`), and
  -- letting time pass keeps it reducible (`DELAY`).

  store-alloc : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
              → Store St
              → Val A (St ⟨ ρ ⟩ₛ) (V-rename (eq-ren ++ᶜ-identityˡ) V)
              → Store (St ∷ₛ V)
