------------------------------------------------------------------------
-- The logical relation: reducible values, computations and stores.   --
--                                                                    --
-- Unary and purely syntactic — it only has to deliver weak-head      --
-- normalization; soundness and head-faithfulness are separate.       --
--                                                                    --
-- `Comp` is an inductive family: `E` is an arbitrary preordered      --
-- monoid, so `op-grade op ·ₑ ε` need not exceed `ε` and there is no  --
-- measure to recurse on. Its induction carries FL's `handle` case.   --
--                                                                    --
-- Ground types have no arrows, so `Valᵍ` comes first and `Comp`      --
-- precedes `Val`, which instantiates it at the smaller predicate.    --
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
-- `M` runs to a weak head normal form whose components are reducible. A step
-- only refines the grade, so the whnf's grade and state are bound by the
-- constructors; `steps-≾`/`steps-grade` recover the refinement.

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
-- resource variable (`grad-typ⇒var`) — canonical forms are read off directly.
--
-- Both `⇒` and `[ ρ ]` are Kripke. `[ ρ ]` because the resource is ready only
-- once enough time has passed. `⇒` because `Val` must be monotone: `BOX`
-- allocates a cell, and a function reaching the extended state may be applied
-- to arguments mentioning it.

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
  × (∀ {St'} → (q : Slice St uᵣ St' uᵣ)
     → (W : toCtx St' ⊢V⦂ A) → Val A St' W
     → Comp B (Val B) ε St' ((slice-under q M) [ Hd ↦ W ]c))
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
-- A step in front of a reducible computation reaches the same whnf by a longer
-- run. `Comp` carries runs, so `_◅_` leaves the grade free.

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

-- Ground reducibility is value reducibility at the embedded type: the clauses
-- agree, ground types having no arrow. Needed at `perform` and at a `handle`
-- clause's parameter and resumption.

Valᵍ→Val : ∀ {G St} → (V : toCtx St ⊢V⦂ type-of-gtype G)
         → Valᵍ G St V → Val (type-of-gtype G) St V

Val→Valᵍ : ∀ {G St} → (V : toCtx St ⊢V⦂ type-of-gtype G)
         → Val (type-of-gtype G) St V → Valᵍ G St V

Valᵍ→Val {Base b}      V p = tt
Valᵍ→Val {Unit}        V p = tt
Valᵍ→Val {Empty}       V p = tt
Valᵍ→Val {G₁ |×|ᵍ G₂}  V (V₁ , V₂ , e , p₁ , p₂) =
  V₁ , V₂ , e , Valᵍ→Val V₁ p₁ , Valᵍ→Val V₂ p₂
Valᵍ→Val {[ ρ ]ᵍ G}    V p = λ q → Valᵍ→Val _ (p q)

Val→Valᵍ {Base b}      V p = tt
Val→Valᵍ {Unit}        V p = tt
Val→Valᵍ {Empty}       V p = tt
Val→Valᵍ {G₁ |×|ᵍ G₂}  V (V₁ , V₂ , e , p₁ , p₂) =
  V₁ , V₂ , e , Val→Valᵍ V₁ p₁ , Val→Valᵍ V₂ p₂
Val→Valᵍ {[ ρ ]ᵍ G}    V p = λ q → Val→Valᵍ _ (p q)

postulate

  -- Monotonicity along a unit slice, used by `BOX`. Recursion on `A`, needing
  -- two syntactic lemmas: functoriality of renaming
  -- (`C-rename (r ∘ʳ r') ≡ C-rename r ∘ C-rename r'`, absent from
  -- `Syntax.RenActions`) for `⇒`, and coherence of `unbox-lookup` with slice
  -- composition for `[ ρ ]`.

  Val-slice : ∀ {A St St'} → (q : Slice St uᵣ St' uᵣ) → (V : toCtx St ⊢V⦂ A)
            → Val A St V → Val A St' (slice-val q V)

  -- The store makes every resource variable reducible: this is what discharges
  -- `Val`'s `[ ρ ]` clause in the variable case of the fundamental lemma.

  store-var : ∀ {A ρ ρ'} {St : 𝕊 []}
            → Store St
            → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
            → (f : ¬ Eternal ([ ρ ] A) → ρ' ≾ᵣ uᵣ)
            → Val ([ ρ ] A) St (var f x)

-- Allocation extends a reducible store with a reducible value (`BOX`): a cell
-- is its stored value, so this is the pair.

store-alloc : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → Store St
            → Val A (St ⟨ ρ ⟩ₛ) (V-rename (eq-ren ++ᶜ-identityˡ) V)
            ------------------------------------------------------
            → Store (St ∷ₛ V)
store-alloc V pSt pV = pSt , pV
