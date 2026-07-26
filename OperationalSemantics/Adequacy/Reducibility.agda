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
open import OperationalSemantics.Adequacy.SubEquivalence  Spec
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

-- A whole run in front of a reducible computation, and transporting one along an
-- equality of effects (which `SEQ-OP`'s reduct carries).

Comp-expand* : ∀ {A P ε ε'} {St St' : 𝕊 []}
             → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
             → ⟨ St , M ⟩ ↝* ⟨ St' , M' ⟩
             → Comp A P ε' St' M'
             -------------------------
             → Comp A P ε St M

Comp-expand* ε*       p = p
Comp-expand* (r ◅ rs) p = Comp-expand r (Comp-expand* rs p)

Comp-ε-subst : ∀ {A P ε ε'} {St : 𝕊 []} → (e : ε ≡ ε')
             → {M : toCtx St ⊢C⦂ A ‼ ε}
             → Comp A P ε St M → Comp A P ε' St (ε-subst e M)
Comp-ε-subst refl p = p

-- The empty store: `toCtx ∅` has no variables.

store-∅ : Store ∅
store-∅ x f = ⊥-elim (not-in-empty-ctx x)

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

-- COMPUTATIONS ACROSS THE STATE EQUIVALENCE
--
-- One lemma carrying *both* relations: the states' and the terms'. They cannot
-- be separated — the `comp-op` case replays the resumption's slice and recurses,
-- and the two continuations come out of `≐-perform⁻` related only by `_≐ᶜ_`.
--
-- Parameterised by the value predicate's transport rather than mutual with
-- `Val-≐ˢ`, so that both recurse structurally on the *type*.

≡→≐ᶜ : ∀ {Γ C} {M M' : Γ ⊢C⦂ C} → M ≡ M' → M ≐ᶜ M'
≡→≐ᶜ refl = ≐ᶜ-refl _

-- The reduct a resumption builds, compared across the two states.

resume-≐ : ∀ {A B ε ρ} {St St' St₂ St₂' : 𝕊 []}
         → (es : St ≐ˢ St') → (es₂ : St₂ ≐ˢ St₂')
         → {q : Slice St ρ St₂ ρ} → {q' : Slice St' ρ St₂' ρ}
         → ext q ≤≐ ext q'
         → {M : toCtx St ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε}
         → {M' : toCtx St' ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε}
         → M ≐ᶜ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ρ ⟩ ∷ B) (sym (toCtx-≐ˢ es))) M'
         → {W : toCtx (St₂ ⟨ ρ ⟩ₛ) ⊢V⦂ B} → {W' : toCtx (St₂' ⟨ ρ ⟩ₛ) ⊢V⦂ B}
         → W ≐ᵛ castᵛ (cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es₂))) W'
         -------------------------------------------------------------------
         → resume q M W
         ≐ᶜ castᶜ (cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es₂))) (resume q' M' W')

resume-≐ {A} {B} {ρ = ρ} es es₂ {q} {q'} h {M} {M'} eM {W} {W'} eW =
  ≐ᶜ-trans
    (sub-≐ᶜ Hd eW
      (≐ᶜ-trans (C-rename-≐ (cong-∷-ren-≐ (suc-comp-ren-≐ h es es₂ _ _)) M)
                (C-rename-cong (cong-∷-ren _)
                  (subst (λ z → M ≐ᶜ z)
                         (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ ρ ⟩ ∷ B)
                                          (sym (toCtx-≐ˢ es)))
                                    (cong (_∷ B) e₁) M')
                         eM))))
    (≡→≐ᶜ (trans (cong (λ z → z [ Hd ↦ castᵛ e₂ W' ]c)
                       (cast-rename-∷ e₁ e₂ (slice-ren q') M'))
                 (cast-app e₂ (C-rename (cong-∷-ren (slice-ren q')) M') W')))
  where
    e₁ = cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es))
    e₂ = cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es₂))

Comp-≐ : ∀ {A P ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
       → (tr : ∀ {St₁ St₁' : 𝕊 []} → (es₁ : St₁ ≐ˢ St₁')
             → (V : toCtx St₁ ⊢V⦂ A) → P St₁ V
             → P St₁' (castᵛ (toCtx-≐ˢ es₁) V))
       → (tr≐ : ∀ {St₁ : 𝕊 []} {V V' : toCtx St₁ ⊢V⦂ A}
              → V ≐ᵛ V' → P St₁ V → P St₁ V')
       → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
       → M ≐ᶜ castᶜ (sym (toCtx-≐ˢ es)) M'
       -------------------------------------------------------------
       → Comp A P ε St M → Comp A P ε St' M'

Comp-≐ es tr tr≐ eM (comp-ret rs pV) with ↝*-≐ es eM rs
... | St₁' , N' , es₁ , rs' , eN with ≐-return⁻ (sym (toCtx-≐ˢ es₁)) N' eN
...   | V' , refl , eV =
  comp-ret rs'
    (tr≐ (subst (λ z → castᵛ (toCtx-≐ˢ es₁) _ ≐ᵛ z)
                (castᵛ-castᵛ (sym (toCtx-≐ˢ es₁)) (toCtx-≐ˢ es₁) V')
                (castᵛ-≐ (toCtx-≐ˢ es₁) eV))
         (tr es₁ _ pV))

Comp-≐ {A} {P} es tr tr≐ eM (comp-op {op = op} {M' = Mk} rs pW pk)
  with ↝*-≐ es eM rs
... | St₁' , N' , es₁ , rs' , eN with ≐-perform⁻ (sym (toCtx-≐ˢ es₁)) N' eN
...   | W' , Mk' , refl , eW , eMk =
  comp-op rs'
    (Valᵍ-≐ᵛ (param op)
      (subst (λ z → castᵛ (toCtx-≐ˢ es₁) _ ≐ᵛ z)
             (castᵛ-castᵛ (sym (toCtx-≐ˢ es₁)) (toCtx-≐ˢ es₁) W')
             (castᵛ-≐ (toCtx-≐ˢ es₁) eW))
      (Valᵍ-≐ˢ es₁ (param op) _ pW))
    (λ q' W'' pW'' → step q' W'' pW'')
  where
    ρ = mapᵉ (op-grade op)

    step : ∀ {St₂ : 𝕊 []} → (q' : Slice _ ρ St₂ ρ)
         → (W'' : toCtx (St₂ ⟨ ρ ⟩ₛ) ⊢V⦂ type-of-gtype (arity op))
         → Valᵍ (arity op) (St₂ ⟨ ρ ⟩ₛ) W''
         → Comp A P _ (St₂ ⟨ ρ ⟩ₛ) (resume q' Mk' W'')
    step {St₂} q' W'' pW'' with slice-replay (≐ˢ-sym es₁) q'
    ... | St₃ , q , es₃ , h =
      Comp-≐ (≐ˢ-sym esL) tr tr≐
        (subst (λ z → resume q Mk (castᵛ (toCtx-≐ˢ esL) W'') ≐ᶜ z)
               (castᶜ-irr (cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ (≐ˢ-sym es₃))))
                          (sym (toCtx-≐ˢ (≐ˢ-sym esL)))
                          (resume q' Mk' W''))
          (resume-≐ es₁ (≐ˢ-sym es₃) (≤≐-sym h) eMk
            (subst (λ z → castᵛ (toCtx-≐ˢ esL) W'' ≐ᵛ z)
                   (castᵛ-irr (toCtx-≐ˢ esL)
                              (cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ (≐ˢ-sym es₃))))
                              W'')
                   (≐ᵛ-refl _))))
        (pk q (castᵛ (toCtx-≐ˢ esL) W'')
             (Valᵍ-≐ˢ esL (arity op) W'' pW''))
      where
        esL = ⟨⟩-≐ˢ ρ es₃

-- VALUES ACROSS THE STATE EQUIVALENCE
--
-- Recursion on the type. Both Kripke clauses replay the other state's extension
-- and transport back; the arrow clause is where `Comp-≐` is called, at the
-- smaller type `B`, which is what keeps the two definitions non-mutual.

Val-≐ˢ : ∀ {St St' : 𝕊 []} → (es : St ≐ˢ St') → (A : VType)
       → (V : toCtx St ⊢V⦂ A)
       → Val A St V → Val A St' (castᵛ (toCtx-≐ˢ es) V)

Val-≐ˢ es (Base b)  V p = tt
Val-≐ˢ es Unit      V p = tt
Val-≐ˢ es Empty     V p = tt
Val-≐ˢ es (A |×| B) .(⦉ V₁ , V₂ ⦊) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , castᵛˢ-pair (toCtx-≐ˢ es) V₁ V₂
  , Val-≐ˢ es A V₁ p₁ , Val-≐ˢ es B V₂ p₂

Val-≐ˢ {St} {St'} es (A ⇒ (B ‼ ε)) .(lam M) (M , refl , f) =
    _ , castᵛ-lam (toCtx-≐ˢ es) M
  , λ {St''} q' M₂ eM₂ W pW → step q' M₂ eM₂ W pW
  where
    e = toCtx-≐ˢ es

    step : ∀ {St'' : 𝕊 []} → (q' : Slice St' uᵣ St'' uᵣ)
         → (M₂ : toCtx St'' ∷ A ⊢C⦂ B ‼ ε)
         → M₂ ≐ᶜ slice-under q' (castᶜ (cong (_∷ A) e) M)
         → (W : toCtx St'' ⊢V⦂ A) → Val A St'' W
         → Comp B (Val B) ε St'' (M₂ [ Hd ↦ W ]c)
    step {St''} q' M₂ eM₂ W pW with slice-replay (≐ˢ-sym es) q'
    ... | St₂ , q , es₂ , h =
      Comp-≐ (≐ˢ-sym es₂) (λ es₁ V₀ → Val-≐ˢ es₁ B V₀) (Val-≐ᵛ B)
        (≡→≐ᶜ (trans (cast-app e₂ M₂ W)
                     (castᶜ-irr e₂ (sym (toCtx-≐ˢ (≐ˢ-sym es₂)))
                                (M₂ [ Hd ↦ W ]c))))
        (f q (castᶜ (cong (_∷ A) e₂) M₂) eM₃ (castᵛ e₂ W)
             (Val-≐ˢ es₂ A W pW))
      where
        e₂ = toCtx-≐ˢ es₂

        eM₃ : castᶜ (cong (_∷ A) e₂) M₂ ≐ᶜ slice-under q M
        eM₃ =
          ≐ᶜ-trans (castᶜ-≐ (cong (_∷ A) e₂) eM₂)
            (≐ᶜ-trans
              (≡→≐ᶜ (sym (cast-rename-∷ (sym e) e₂ (slice-renᵘ q')
                                        (castᶜ (cong (_∷ A) e) M))))
              (≐ᶜ-trans
                (≡→≐ᶜ (cong (C-rename
                              (cong-∷-ren (castʳ² (sym e) e₂ (slice-renᵘ q'))))
                            (castᶜ-castᶜ (cong (_∷ A) e) (cong (_∷ A) (sym e)) M)))
                (≐ᶜ-sym
                  (C-rename-≐
                    (cong-∷-ren-≐
                      (≐ʳ-trans (slice-renᵘ-≐ˢ es (≐ˢ-sym es₂) (≤≐-sym h))
                                (castʳ²-irr (sym e) (sym e)
                                            (sym (toCtx-≐ˢ (≐ˢ-sym es₂))) e₂
                                            (slice-renᵘ q'))))
                    M))))

Val-≐ˢ {St} {St'} es ([ ρ ] A) V f {St''} q' W eW
  with slice-replay (≐ˢ-sym es) q'
... | St₂ , q , es₂ , h =
  subst (Val A St'')
        (castᵛ-castᵛ (toCtx-≐ˢ es₂) (toCtx-≐ˢ (≐ˢ-sym es₂)) W)
        (Val-≐ˢ (≐ˢ-sym es₂) A (castᵛ (toCtx-≐ˢ es₂) W)
          (f q (castᵛ (toCtx-≐ˢ es₂) W) eW₂))
  where
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

-- Hence reducibility is insensitive to the term equivalence: the special case
-- `es := ≐ˢ-refl St`, where `toCtx-≐ˢ-refl` makes the cast the identity.

Comp-≐ᶜ : ∀ {A ε} {St : 𝕊 []} {M M' : toCtx St ⊢C⦂ A ‼ ε}
        → M ≐ᶜ M' → Comp' A ε St M → Comp' A ε St M'
Comp-≐ᶜ {A} {ε} {St} {M} {M'} eM pM =
  Comp-≐ (≐ˢ-refl St) (λ es₁ V₀ → Val-≐ˢ es₁ A V₀) (Val-≐ᵛ A)
    (subst (λ z → M ≐ᶜ castᶜ (sym z) M') (sym (toCtx-≐ˢ-refl St)) eM)
    pM

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
-- What is left is one renaming agreement, best stated as its own lemma about
-- *any* already-allocated cell rather than the fresh one:
--
--   lookup-slice : (e : St₀ ≤ₛ St₂) → (c : [ ρ ] A ∈[ σ ] toCtx St₀) → …
--                → lookup-body St₂ (≤ₛ-embed e c) _
--                ≐ᵛ V-rename (unbox-ren (slice e b)) (lookup-body St₀ c _)
--
-- "reading an already-allocated cell in a later state is reading it in the
-- earlier one and transporting". `store-fresh` is the case `St₀ := St ∷ₛ V`,
-- `c := Hd`, where `lookup-body St₀ Hd _` is `V` renamed. By induction on `e`:
-- each `≤ₛ` step grows `split-state-snd` by exactly what `suc-comp-ren` adds, so
-- the two renamings stay in step. `wk-ren-⟨ρ⟩-ctx-tgt` (in `Slice`) computes the
-- lookup side of that on a variable; `≤ₛ-embed-fst`/`≤ₛ-embed-lookup` already
-- give the value side.

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
