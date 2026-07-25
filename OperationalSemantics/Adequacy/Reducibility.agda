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

open import OperationalSemantics.Adequacy.RenEquivalence   Spec
open import OperationalSemantics.Adequacy.Slice           Spec
open import OperationalSemantics.Adequacy.StateEquivalence Spec

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

-- REDUCIBLE STORES
--
-- Every resource variable of the state context is reducible. Stated on the
-- variables rather than by recursion on `𝕊`, because reducibility of a cell is
-- a Kripke statement — the value is read back by `unbox-lookup` at a *later*
-- state — and that is exactly `Val` at the cell's box type. The store is the
-- closing environment for the resource variables of `toCtx St`.

Store : 𝕊 [] → Set
Store St = ∀ {A ρ} → (x : A ∈[ ρ ] toCtx St) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
         → Val A St (var f x)

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

-- The empty store: `toCtx ∅` has no variables.

store-∅ : Store ∅
store-∅ x f = ⊥-elim (not-in-empty-ctx x)

postulate

  -- Reducibility is insensitive to the term equivalence. `↝*-≐` transports the
  -- run, but its whnf sits at a state only `_≐ˢ_`-related to the original's
  -- (`BOX` stores `_≐ᵛ_`-related values), so the whnf's components have to be
  -- moved across `_≐ˢ_` too. That is the one remaining semantic obligation —
  -- `Val-≐`/`Comp-≐` of the plan's item 4, to be proved *non*-mutually, passing
  -- `Val-≐ A` to `Comp-≐` as a parameter.

  Comp-≐ᶜ : ∀ {A ε} {St : 𝕊 []} {M M' : toCtx St ⊢C⦂ A ‼ ε}
          → M ≐ᶜ M' → Comp' A ε St M → Comp' A ε St M'

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

-- Looking a resource up consults the boxed value only through `unbox⇒var`,
-- which sees it as a variable (`grad-typ⇒var`), so `_≐ᵛ_`-related values give
-- the same cell — and the recovered grade bound reaches only a `⟨⟩-≤-ren`.

unbox-lookup-val-≐ : ∀ {A ρ Δ} {St : 𝕊 []}
                   → (w : Ren (Δ ⟨ ρ ⟩) (toCtx St))
                   → {V V' : Δ ⊢V⦂ [ ρ ] A} → V ≐ᵛ V'
                   → unbox-lookup St w V ≐ᵛ unbox-lookup St w V'

unbox-lookup-val-≐ {St = St} w (var-≐ {x = x})
  with var-rename w (Tl-⟨⟩ x)
... | ρ' , p , z =
  V-rename-≐
    (∘ʳ-≐ ≐ʳ-refl
      (∘ʳ-≐ ≐ʳ-refl
        (∘ʳ-≐ ≐ʳ-refl
          (∘ʳ-≐ (⟨⟩-≤-ren-≐ _ _) ≐ʳ-refl))))
    (resource-lookup St z)

-- Renaming the boxed value before looking it up is looking it up along the
-- composed slice. Unfolding the lookup (`unbox-lookup-≡`) leaves the cell,
-- which is the same by `unbox-cellsᵛ`, and the grade bound, which is
-- irrelevant — so the two values are equal, not merely equivalent.

unbox-lookup-ren : ∀ {A ρ} {St St' St₂ : 𝕊 []}
                 → (q₀ : Slice St uᵣ St' uᵣ) → (q' : Slice St' ρ St₂ uᵣ)
                 → (V : toCtx St ⊢V⦂ [ ρ ] A)
                 → unbox-lookup St₂ (unbox-ren q') (slice-val q₀ V)
                 ≡ unbox-lookup St₂ (unbox-ren (slice-∘ᵘ q' q₀)) V

unbox-lookup-ren {St₂ = St₂} q₀ q' V =
  trans (unbox-lookup-≡ St₂ (unbox-ren q') (slice-val q₀ V))
    (trans (lookup-body-≡ St₂ (unbox-cellsᵛ q₀ q' V) _ _)
           (sym (unbox-lookup-≡ St₂ (unbox-ren (slice-∘ᵘ q' q₀)) V)))

-- ETERNAL TYPES ARE FREE
--
-- An eternal type is built from base, unit, empty and products, so `Val` asks
-- nothing of a value of eternal type — except, at a product, that it *be* a
-- pair, which over a state context it is (`⦉⦊-not-in-toCtx`). This is what
-- makes the eternal zone of an environment reducible for nothing, and what
-- covers the variables a lock would otherwise block.

pair-canonical : ∀ {A B} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ A |×| B)
               → Σ[ V₁ ∈ toCtx St ⊢V⦂ A ] Σ[ V₂ ∈ toCtx St ⊢V⦂ B ]
                   (V ≡ ⦉ V₁ , V₂ ⦊)
pair-canonical (var f x) = ⊥-elim (⦉⦊-not-in-toCtx x)
pair-canonical ⦉ V , W ⦊  = V , W , refl

-- There is no value of the empty type over a state context: a variable is ruled
-- out by `Empty-not-in-toCtx` and no other value has that type. This is what
-- discharges `absurd`, which has no reduction rule.

empty-canonical : ∀ {St : 𝕊 []} → toCtx St ⊢V⦂ Empty → ⊥
empty-canonical (var f x) = Empty-not-in-toCtx x

Val-eternal : ∀ {A} {St : 𝕊 []} → Eternal A → (V : toCtx St ⊢V⦂ A) → Val A St V

Val-eternal (Baseₑ b _)      V = tt
Val-eternal Unitₑ            V = tt
Val-eternal Emptyₑ           V = tt
Val-eternal (et₁ |×|ₑ et₂)   V with pair-canonical V
... | V₁ , V₂ , refl           =
  V₁ , V₂ , refl , Val-eternal et₁ V₁ , Val-eternal et₂ V₂

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
  λ q' W eW →
    f (slice-∘ᵘ q' q₀) W
      (subst (λ z → W ≐ᵛ z) (unbox-lookup-ren q₀ q' V) eW)

-- GROUND TYPES
--
-- `Valᵍ` is `Val` restricted to the ground types, whose formation rules
-- `type-of-gtype` matches one for one. Two recursions on the ground type, needed
-- because `Comp`'s operation constructor speaks of `Valᵍ` while the fundamental
-- lemma delivers `Val`.

Val→Valᵍ : (G : GType) → {St : 𝕊 []} → (V : toCtx St ⊢V⦂ type-of-gtype G)
         → Val (type-of-gtype G) St V → Valᵍ G St V

Val→Valᵍ (Base b)     V p = tt
Val→Valᵍ Unit         V p = tt
Val→Valᵍ Empty        V p = tt
Val→Valᵍ (G₁ |×|ᵍ G₂) V (V₁ , V₂ , refl , p₁ , p₂) =
  V₁ , V₂ , refl , Val→Valᵍ G₁ V₁ p₁ , Val→Valᵍ G₂ V₂ p₂
Val→Valᵍ ([ ρ ]ᵍ G)   V p = λ q W eW → Val→Valᵍ G W (p q W eW)

Valᵍ→Val : (G : GType) → {St : 𝕊 []} → (V : toCtx St ⊢V⦂ type-of-gtype G)
         → Valᵍ G St V → Val (type-of-gtype G) St V

Valᵍ→Val (Base b)     V p = tt
Valᵍ→Val Unit         V p = tt
Valᵍ→Val Empty        V p = tt
Valᵍ→Val (G₁ |×|ᵍ G₂) V (V₁ , V₂ , refl , p₁ , p₂) =
  V₁ , V₂ , refl , Valᵍ→Val G₁ V₁ p₁ , Valᵍ→Val G₂ V₂ p₂
Valᵍ→Val ([ ρ ]ᵍ G)   V p = λ q W eW → Valᵍ→Val G W (p q W eW)

-- Ground reducibility is insensitive to the equivalence, as `Val-≐ᵛ` is.

Valᵍ-≐ᵛ : ∀ {St : 𝕊 []} → (G : GType) → {V V' : toCtx St ⊢V⦂ type-of-gtype G}
        → V ≐ᵛ V' → Valᵍ G St V → Valᵍ G St V'

Valᵍ-≐ᵛ (Base b)     eV p = tt
Valᵍ-≐ᵛ Unit         eV p = tt
Valᵍ-≐ᵛ Empty        eV p = tt
Valᵍ-≐ᵛ (G₁ |×|ᵍ G₂) (pair-≐ e₁ e₂) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , refl , Valᵍ-≐ᵛ G₁ e₁ p₁ , Valᵍ-≐ᵛ G₂ e₂ p₂
Valᵍ-≐ᵛ ([ ρ ]ᵍ G)   eV f =
  λ q W eW → f q W (≐ᵛ-trans eW (unbox-lookup-val-≐ (unbox-ren q) (≐ᵛ-sym eV)))

-- GROUND VALUES ACROSS THE STATE EQUIVALENCE
--
-- Related states hold related values, so reducibility transports. Recursion on
-- the ground type; the box clause replays the slice on the other state
-- (`slice-replay` + `≐ˢ-sym`), moves the boxed value there
-- (`unbox-lookup-cast-val`), and identifies the two reads
-- (`unbox-ren-bridge`, then `unbox-lookup-≐`).

Valᵍ-≐ˢ : ∀ {St St' : 𝕊 []} → (es : St ≐ˢ St') → (G : GType)
        → (V : toCtx St ⊢V⦂ type-of-gtype G)
        → Valᵍ G St V → Valᵍ G St' (castᵛ (toCtx-≐ˢ es) V)

Valᵍ-≐ˢ es (Base b)     V p = tt
Valᵍ-≐ˢ es Unit         V p = tt
Valᵍ-≐ˢ es Empty        V p = tt
Valᵍ-≐ˢ es (G₁ |×|ᵍ G₂) .(⦉ V₁ , V₂ ⦊) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , castᵛˢ-pair (toCtx-≐ˢ es) V₁ V₂
  , Valᵍ-≐ˢ es G₁ V₁ p₁ , Valᵍ-≐ˢ es G₂ V₂ p₂

Valᵍ-≐ˢ {St} {St'} es ([ ρ ]ᵍ G) V f {St''} q' W eW
  with slice-replay (≐ˢ-sym es) q'
... | St₂ , q , es₂ , h =
  subst (Valᵍ G St'')
        (castᵛ-castᵛ (toCtx-≐ˢ es₂) (toCtx-≐ˢ (≐ˢ-sym es₂)) W)
        (Valᵍ-≐ˢ (≐ˢ-sym es₂) G (castᵛ (toCtx-≐ˢ es₂) W)
          (f q (castᵛ (toCtx-≐ˢ es₂) W) eW₂))
  where
    -- the read at `St''` is the read at `St₂`, moved back
    eW₂ : castᵛ (toCtx-≐ˢ es₂) W ≐ᵛ unbox-lookup St₂ (unbox-ren q) V
    eW₂ =
      subst (λ z → castᵛ (toCtx-≐ˢ es₂) W ≐ᵛ z)
            (castᵛ-castᵛ (sym (toCtx-≐ˢ es₂)) (toCtx-≐ˢ es₂)
                         (unbox-lookup St₂ (unbox-ren q) V))
            (castᵛ-≐ (toCtx-≐ˢ es₂)
              (≐ᵛ-trans eW
                (≐ᵛ-trans
                  (unbox-lookup-cast-val St'' (toCtx-≐ˢ es) (unbox-ren q') V)
                  (unbox-lookup-≐ es₂ (unbox-ren-bridge es es₂ h) V))))

-- COMPUTATIONS ACROSS THE STATE EQUIVALENCE (next step)
--
-- `Comp-≐ᶜ` below must be proved as one lemma carrying *both* relations at
-- once — the state equivalence and the term equivalence:
--
--   Comp-≐ : (es : St ≐ˢ St') → (tr : P transports along `_≐ˢ_`)
--          → (tr≐ : P respects `_≐ᵛ_`)
--          → M ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) M' → Comp A P ε St M
--          → Comp A P ε St' M'
--
-- Separating them does not work: the `comp-op` case replays the resumption's
-- slice on the other state and recurses, and the two resumptions' continuations
-- are related only by `_≐ᶜ_` (they come from `≐-perform⁻`), never equal — so the
-- recursive call needs the term relation in hand. `Comp-≐ᶜ` is then the special
-- case `es := ≐ˢ-refl St`, where `toCtx-≐ˢ-refl` makes the cast the identity.
--
-- It stays parameterised by `P`'s transport rather than mutual with `Val-≐ˢ`,
-- so that both recurse structurally on the *type*: `Val-≐ˢ` at `⇒` calls it with
-- `Val-≐ˢ B`, at `[ ρ ]` with `Val-≐ˢ A`. Made mutual, the checker would see the
-- cycle `Comp-≐ A → Val-≐ˢ A → Comp-≐ A`.
--
-- Everything the Kripke clauses need is now proved: `Valᵍ-≐ˢ`/`Valᵍ-≐ᵛ` above,
-- and `unbox-lookup-≐`, `unbox-lookup-cast-val`, `unbox-ren-bridge`,
-- `slice-replay` in `Slice`/`StateEquivalence`. What is left is the `comp-op`
-- resumption: replay the slice, transport the arity value, and relate the two
-- `resume`s (`suc-comp-ren-≐` for the renamings, `C-rename-cong` and `sub-≐ᶜ`
-- for the continuation and the value).

-- ALLOCATION
--
-- `BOX` extends the store with a value that is reducible at every state the
-- lock it was boxed under permits — which is what the fundamental lemma
-- supplies, by running its own value case at each such state.
--
-- The old variables are covered by `Val-slice` along the allocation, once the
-- renaming is seen to send a variable to its own weakening. The new one is the
-- lookup at the freshly allocated cell.

alloc-var-≐ : ∀ {A A' ρ ρ'} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → (x : A' ∈[ ρ' ] toCtx St) → (f : ¬ Eternal A' → ρ' ≾ᵣ uᵣ)
            → slice-val (alloc-slice V) (var f x) ≐ᵛ var f (Tl-∷ x)
alloc-var-≐ V x f =
  var-ren-tgt-≐ (slice-renᵘ (alloc-slice V)) x f
                (slice-renᵘ-tgt (alloc-slice V) x) f

-- The freshly allocated cell is reducible: a slice out of `St ∷ₛ V` at `ρ` is
-- one out of `St` (`slice-∘ᵘ` against `alloc-slice`), and reading the cell back
-- returns the stored value. Which cell is read is settled — `unbox-ren-tgt`
-- sends it to `≤ₛ-embed (ext q) Hd` — and what it holds is settled too, by
-- `≤ₛ-embed-fst`/`≤ₛ-embed-lookup`: the cell is split off at `St` and holds `V`,
-- however far the state has grown.
--
-- What is left is one renaming agreement. `lookup-body` transports the stored
-- value by `wk-ren-⟨ρ⟩-ctx` past the cell and everything allocated after it
-- (`split-state-snd`), then reindexes by `split-state-++ᶜ`; the hypothesis
-- transports it by `unbox-ren (slice-∘ᵘ q (alloc-slice V))`, i.e. by
-- `≤ₛ-embed (ext q)`. Both are the same inclusion, but seeing that means
-- relating `split-state-snd St₂` to the part of the extension after the
-- allocation — the last piece of knot 3.

postulate

  store-fresh : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
              → (∀ {St'} → (q : Slice St ρ St' uᵣ)
                   → Val A St' (V-rename (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ) V))
              → (f : ¬ Eternal ([ ρ ] A) → uᵣ ≾ᵣ uᵣ)
              ------------------------------------------
              → Val ([ ρ ] A) (St ∷ₛ V) (var f Hd)

store-alloc : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → Store St
            → (∀ {St'} → (q : Slice St ρ St' uᵣ)
                 → Val A St' (V-rename (unbox-ren q ∘ʳ eq-ren ++ᶜ-identityˡ) V))
            ------------------------------------------------------------------
            → Store (St ∷ₛ V)

store-alloc V pSt pV Hd       f = store-fresh V pV f
store-alloc V pSt pV (Tl-∷ x) f =
  Val-≐ᵛ _ (alloc-var-≐ V x f) (Val-slice (alloc-slice V) (var f x) (pSt x f))
