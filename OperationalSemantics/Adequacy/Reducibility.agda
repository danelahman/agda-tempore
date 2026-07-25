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

open import OperationalSemantics.Adequacy.RenEquivalence Spec
open import OperationalSemantics.Adequacy.Slice         Spec

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
  ∀ {St'} → (q : Slice St ρ St' uᵣ)
  → (W : toCtx St' ⊢V⦂ type-of-gtype G) → W ≐ᵛ unbox-lookup St' (unbox-ren q) V
  → Valᵍ G St' W

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
--
-- Both clauses take their transported term up to `_≐_` rather than on the nose.
-- That is what makes `Val-slice` compose two transports: renaming is functorial
-- only up to `_≐ᶜ_` (`unbox` stores a renaming), so with the slack the composite
-- is reached by `≐-trans` instead of needing `Comp` to respect `_≐ᶜ_`.

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
     → (M₂ : toCtx St' ∷ A ⊢C⦂ B ‼ ε) → M₂ ≐ᶜ slice-under q M
     → (W : toCtx St' ⊢V⦂ A) → Val A St' W
     → Comp B (Val B) ε St' (M₂ [ Hd ↦ W ]c))
Val ([ ρ ] A)     St V =
  ∀ {St'} → (q : Slice St ρ St' uᵣ)
  → (W : toCtx St' ⊢V⦂ A) → W ≐ᵛ unbox-lookup St' (unbox-ren q) V
  → Val A St' W

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

postulate

  -- Looking a resource up is coherent: it consults the boxed value only through
  -- `unbox⇒var` (so up to `_≐ᵛ_`), and renaming that value before looking it up
  -- is looking it up along the composed slice.

  unbox-lookup-val-≐ : ∀ {A ρ Δ} {St : 𝕊 []}
                     → (w : Ren (Δ ⟨ ρ ⟩) (toCtx St))
                     → {V V' : Δ ⊢V⦂ [ ρ ] A} → V ≐ᵛ V'
                     → unbox-lookup St w V ≐ᵛ unbox-lookup St w V'

  unbox-lookup-ren : ∀ {A ρ} {St St' St₂ : 𝕊 []}
                   → (q₀ : Slice St uᵣ St' uᵣ) → (q' : Slice St' ρ St₂ uᵣ)
                   → (V : toCtx St ⊢V⦂ [ ρ ] A)
                   → unbox-lookup St₂ (unbox-ren q') (slice-val q₀ V)
                   ≐ᵛ unbox-lookup St₂ (unbox-ren (slice-∘ᵘ q' q₀)) V

  -- The store makes every resource variable reducible: this is what discharges
  -- `Val`'s `[ ρ ]` clause in the variable case of the fundamental lemma.

  store-var : ∀ {A ρ ρ'} {St : 𝕊 []}
            → Store St
            → (x : [ ρ ] A ∈[ ρ' ] toCtx St)
            → (f : ¬ Eternal ([ ρ ] A) → ρ' ≾ᵣ uᵣ)
            → Val ([ ρ ] A) St (var f x)

------------------------------------------------------------------------
-- REDUCIBILITY IS INSENSITIVE TO THE EQUIVALENCE, AND MONOTONE
--
-- Both are recursions on the type, and both are almost free: the slack in the
-- two Kripke clauses absorbs exactly the mismatch, so nothing has to be
-- transported. `Val-slice` composes the two slices — `slice-∘` at `⇒` (both
-- unit-graded) and `slice-∘ᵘ` at `[ ρ ]` (the outer one guarded).
------------------------------------------------------------------------

Val-≐ᵛ : ∀ {St : 𝕊 []} → (A : VType) → {V V' : toCtx St ⊢V⦂ A}
       → V ≐ᵛ V' → Val A St V → Val A St V'

Val-≐ᵛ (Base b)  eV p = tt
Val-≐ᵛ Unit      eV p = tt
Val-≐ᵛ Empty     eV p = tt
Val-≐ᵛ (A |×| B) (pair-≐ e₁ e₂) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , refl , Val-≐ᵛ A e₁ p₁ , Val-≐ᵛ B e₂ p₂
Val-≐ᵛ (A ⇒ (B ‼ ε)) (lam-≐ eM) (M , refl , f) =
  _ , refl , λ q M₂ eM₂ W pW →
                f q M₂ (≐ᶜ-trans eM₂ (C-rename-cong (cong-∷-ren _) (≐ᶜ-sym eM))) W pW
Val-≐ᵛ ([ ρ ] A) eV f =
  λ q W eW → f q W (≐ᵛ-trans eW (unbox-lookup-val-≐ (unbox-ren q) (≐ᵛ-sym eV)))

Val-slice : ∀ {A St St'} → (q : Slice St uᵣ St' uᵣ) → (V : toCtx St ⊢V⦂ A)
          → Val A St V → Val A St' (slice-val q V)

Val-slice {Base b}  q V p = tt
Val-slice {Unit}    q V p = tt
Val-slice {Empty}   q V p = tt
Val-slice {A |×| B} q .(⦉ V₁ , V₂ ⦊) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , refl , Val-slice q V₁ p₁ , Val-slice q V₂ p₂
Val-slice {A ⇒ (B ‼ ε)} q₀ .(lam M) (M , refl , f) =
    _ , refl
  , λ q' M₂ eM₂ W pW →
      f (slice-∘ q' q₀) M₂
        (≐ᶜ-trans eM₂
          (≐ᶜ-trans
            (≐ᶜ-sym (C-rename-∘ (cong-∷-ren (slice-renᵘ q'))
                                (cong-∷-ren (slice-renᵘ q₀)) M))
            (C-rename-≐ (≐ʳ-trans
                          (≐ʳ-sym (cong-∷-ren-∘-≐ (slice-renᵘ q') (slice-renᵘ q₀)))
                          (cong-∷-ren-≐ (≐ʳ-sym (slice-renᵘ-∘ q' q₀))))
                        M)))
        W pW
Val-slice {[ ρ ] A} q₀ V f =
  λ q' W eW → f (slice-∘ᵘ q' q₀) W (≐ᵛ-trans eW (unbox-lookup-ren q₀ q' V))

-- Allocation extends a reducible store with a reducible value (`BOX`): a cell
-- is its stored value, so this is the pair.

store-alloc : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → Store St
            → Val A (St ⟨ ρ ⟩ₛ) (V-rename (eq-ren ++ᶜ-identityˡ) V)
            ------------------------------------------------------
            → Store (St ∷ₛ V)
store-alloc V pSt pV = pSt , pV
