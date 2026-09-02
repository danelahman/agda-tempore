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

open import Syntax.Renamings.Equivalence Spec
open import Syntax.Renamings.Coherence   Spec
open import Syntax.Terms.Equivalence     Spec
open import Syntax.Terms.Transport       Spec
open import Syntax.Substitutions.Variables Spec
open import OperationalSemantics.Adequacy.GradedReach           Spec
open import Syntax.Substitutions.Equivalence Spec
open import OperationalSemantics.Adequacy.StateEquivalence Spec

-- REDUCIBLE GROUND VALUES (recursion on `GType`)
--
-- Ground types are the parameter and arity types of operations. They contain
-- no arrows, so this needs nothing but itself — which is what lets `Comp`
-- mention it.

-- THE CELL A BOX-TYPED VALUE NAMES
--
-- A value of box type is always a variable (`grad-typ⇒var`), so it *is* a cell,
-- and that is what both `Val` and `Valᵍ` speak about at a box type.

val-cell : ∀ {Γ A ρ} → Γ ⊢V⦂ [ ρ ] A → Var Γ ([ ρ ] A)
val-cell V = proj₁ (grad-typ⇒var V) , proj₁ (proj₂ (grad-typ⇒var V))

Valᵍ : (G : GType) → (St : 𝕊 []) → toCtx St ⊢V⦂ type-of-gtype G → Set
Valᵍ (Base b)      St V = ⊤
Valᵍ Unit          St V = ⊤
Valᵍ Empty         St V = ⊤
Valᵍ (G₁ |×|ᵍ G₂)  St V =
  Σ[ V₁ ∈ toCtx St ⊢V⦂ type-of-gtype G₁ ]
  Σ[ V₂ ∈ toCtx St ⊢V⦂ type-of-gtype G₂ ]
    (V ≡ ⦉ V₁ , V₂ ⦊) × Valᵍ G₁ St V₁ × Valᵍ G₂ St V₂
Valᵍ ([ ρ ]ᵍ G)    St V =
  ∀ {St'} → (r : St [ proj₂ (val-cell V) ]⊑ᶜ St') → Valᵍ G St' (lookupᶜ r)

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
  -- resumption is reducible at every state where the operation's own grade has
  -- elapsed — the graded reach an `unbox` consumes, since `HANDLE-OP` boxes the
  -- resumption at that grade and a clause reaches it by unboxing

  comp-op : ∀ {ε ε₁} {St St₁ : 𝕊 []} {op : Op}
          → {M : toCtx St ⊢C⦂ A ‼ ε}
          → {W : toCtx St₁ ⊢V⦂ type-of-gtype (param op)}
          → {M' : toCtx St₁ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                    ⊢C⦂ A ‼ ε₁}
          → ⟨ St , M ⟩ ↝* ⟨ St₁ , perform op W M' ⟩
          → Valᵍ (param op) St₁ W
          → (∀ {St₂ : 𝕊 []}
             → (q : St₁ ⊑ₛ[ mapᵉ (op-grade op) ] St₂)
             → (W' : toCtx St₂ ⊢V⦂ type-of-gtype (arity op))
             → Valᵍ (arity op) St₂ W'
             → Comp A P ε₁ St₂ (resume q M' W'))
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
-- The `⇒` clause takes its transported term up to a propositional equation
-- rather than on the nose. That slack is what lets `Val-reach` compose two
-- transports: the two derived renamings agree only up to `_≐ʳ_`, and
-- `C-rename-≡` turns that into the equation the clause asks for.

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
  × (∀ {St'} → (q : St ⊑ₛ[ uᵣ ] St')
     → (M₂ : toCtx St' ∷ A ⊢C⦂ B ‼ ε)
     → M₂ ≡ reach-under q M
     → (W : toCtx St' ⊢V⦂ A)
     → Val A St' W
     → Comp B (Val B) ε St' (M₂ [ split-[] ↦ W ]c))
-- A box type is the cell the value names: readable at a later state means its
-- content is reducible there. This is `Store` below, per cell — `store-var`.
-- Quantifying over `St ⊑ₛ[ ρ ] St'` instead would demand more than
-- readability: that bound is `≤ₛ-grade e ≾ᵣ ρ`, whereas reading a cell gives
-- `proj₁ (≤ₛ-embed e c) ≾ᵣ ρ`, i.e. `σ_c ·ᵣ ≤ₛ-grade e ≾ᵣ ρ`, and with
-- `σ_c ≾ᵣ uᵣ` the latter is strictly weaker.
Val ([ ρ ] A)     St V =
  ∀ {St'} → (r : St [ proj₂ (val-cell V) ]⊑ᶜ St') → Val A St' (lookupᶜ r)

-- Reducible computations at the value predicate `Val` — the form the
-- fundamental lemma proves.

Comp' : (A : VType) → (ε : E) → (St : 𝕊 []) → toCtx St ⊢C⦂ A ‼ ε → Set
Comp' A = Comp A (Val A)

-- REDUCIBLE STORES
--
-- Every cell of the state holds a value that is reducible at any later state
-- at which it is readable. Stated on the cells rather than by recursion on
-- `𝕊`, and on cells alone because every variable of `toCtx St` is of box type
-- (`⇒-not-in-toCtx`, `⦉⦊-not-in-toCtx`, `Empty-not-in-toCtx`).
--
-- The `≤ₛ` is what makes this one condition rather than two. Reading a cell is
-- a Kripke matter — `≤ₛ-embed e x` is where the cell has got to at `St'`, and
-- `rel` says enough time has passed there for a `ρ`-box — and the two ways the
-- development reads a cell are the two ends of that quantification:
--
--   * `e = id-suc` is what `UNBOX` consumes. It fires at the *current* state,
--     and an `unbox` carries only `ρ' ≾ᵣ ρ`, never `ρ' ≾ᵣ uᵣ`: a cell can be
--     readable without being usable as a value.
--
--   * `e = ext q` for a `ρ`-reach `q` is `Val` at the cell's box type, which is
--     `store-var` below. So the reducibility of a box-typed *variable* is this
--     same condition at a later state, not a separate assumption.
--
-- Keeping only the second would not do: instantiating it at the current state
-- needs `St ⊑ₛ[ ρ ] St`, whose bound is `uᵣ ≾ᵣ ρ`, and `Grade` has no such
-- law — rightly, since it would say every box is ready immediately.

Store : 𝕊 [] → Set
Store St = ∀ {A ρ σ} {St' : 𝕊 []} → (c : [ ρ ] A ∈[ σ ] toCtx St)
         → (r : St [ c ]⊑ᶜ St')
         → Val A St' (lookupᶜ r)

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
store-∅ c r = ⊥-elim (not-in-empty-ctx c)

------------------------------------------------------------------------
-- ETERNAL TYPES ARE FREE
--
-- An eternal type is built from base, unit, empty and products, so `Val` asks
-- nothing of a value of eternal type — except, at a product, that it *be* a
-- pair, which over a state context it is (`⦉⦊-not-in-toCtx`). This is what
-- makes the eternal zone of an environment reducible for nothing, and what
-- covers the variables a lock would otherwise block.
------------------------------------------------------------------------

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
-- transported. `Val-reach` composes the two reaches — `reach-∘` at `⇒` (both
-- unit-graded), and at `[ ρ ]` the read's own `≤ₛ-trans`.
------------------------------------------------------------------------

Val-≡ᵛ : ∀ {St : 𝕊 []} → (A : VType) → {V V' : toCtx St ⊢V⦂ A}
       → V ≡ V' → Val A St V → Val A St V'

Val-≡ᵛ A refl p = p

Val-reach : ∀ {A St St'} → (q : St ⊑ₛ[ uᵣ ] St') → (V : toCtx St ⊢V⦂ A)
          → Val A St V → Val A St' (reach-val q V)

Val-reach {Base b}  q V p = tt
Val-reach {Unit}    q V p = tt
Val-reach {Empty}   q V p = tt
Val-reach {A |×| B} q .(⦉ V₁ , V₂ ⦊) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , refl , Val-reach q V₁ p₁ , Val-reach q V₂ p₂
Val-reach {A ⇒ (B ‼ ε)} q₀ .(lam M) (M , refl , f) =
    _ , refl
  , λ q' M₂ eM₂ W pW →
      f (reach-∘ q' q₀) M₂
        (trans eM₂
          (trans
            (sym (C-rename-∘ (cong-∷-ren (reach-renᵘ q₀))
                                (cong-∷-ren (reach-renᵘ q')) M))
            (C-rename-≡ (≐ʳ-trans
                          (≐ʳ-sym (cong-∷-ren-∘-≐ʳ (reach-renᵘ q₀) (reach-renᵘ q')))
                          (cong-∷-ren-≐ʳ (≐ʳ-sym (reach-renᵘ-∘ q' q₀))))
                        M)))
        W pW
Val-reach {[ ρ ] A} q₀ V f {St''} (read e rel) with grad-typ⇒var V
... | _ , c , g , refl =
  Val-≡ᵛ A ((lookup-body-≡ St'' cellEq rel₁ rel))
           (f (read (≤ₛ-trans (ext q₀) e) rel₁))
  where
    cellEq = trans (≤ₛ-embed-∘ (ext q₀) e c)
                   (sym (cong (λ z → ≤ₛ-embed e (proj₂ z))
                              (reach-renᵘ-img q₀ c)))
    rel₁ = subst (_≾ᵣ ρ) (sym (cong proj₁ cellEq)) rel

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
Val→Valᵍ ([ ρ ]ᵍ G)   V p = λ r → Val→Valᵍ G _ (p r)

Valᵍ→Val : (G : GType) → {St : 𝕊 []} → (V : toCtx St ⊢V⦂ type-of-gtype G)
         → Valᵍ G St V → Val (type-of-gtype G) St V

Valᵍ→Val (Base b)     V p = tt
Valᵍ→Val Unit         V p = tt
Valᵍ→Val Empty        V p = tt
Valᵍ→Val (G₁ |×|ᵍ G₂) V (V₁ , V₂ , refl , p₁ , p₂) =
  V₁ , V₂ , refl , Valᵍ→Val G₁ V₁ p₁ , Valᵍ→Val G₂ V₂ p₂
Valᵍ→Val ([ ρ ]ᵍ G)   V p = λ r → Valᵍ→Val G _ (p r)

-- Ground reducibility is insensitive to the equivalence, as `Val-≡ᵛ` is.

Valᵍ-≡ᵛ : ∀ {St : 𝕊 []} → (G : GType) → {V V' : toCtx St ⊢V⦂ type-of-gtype G}
        → V ≡ V' → Valᵍ G St V → Valᵍ G St V'

Valᵍ-≡ᵛ G refl p = p

-- GROUND VALUES ACROSS THE STATE EQUIVALENCE
--
-- Related states hold related values, so reducibility transports. Recursion on
-- the ground type; the box clause replays the reach on the other state
-- (`reach-replay` + `≐ˢ-sym`) and identifies the two reads (`unbox-ren-bridge`,
-- then `lookup-body-≐ˢ`).

Valᵍ-≐ˢ : ∀ {St St' : 𝕊 []} → (es : St ≐ˢ St') → (G : GType)
        → (V : toCtx St ⊢V⦂ type-of-gtype G)
        → Valᵍ G St V → Valᵍ G St' (castᵛ (toCtx-≐ˢ es) V)

Valᵍ-≐ˢ es (Base b)     V p = tt
Valᵍ-≐ˢ es Unit         V p = tt
Valᵍ-≐ˢ es Empty        V p = tt
Valᵍ-≐ˢ es (G₁ |×|ᵍ G₂) .(⦉ V₁ , V₂ ⦊) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , cast-pair (toCtx-≐ˢ es) {V₁} {V₂}
  , Valᵍ-≐ˢ es G₁ V₁ p₁ , Valᵍ-≐ˢ es G₂ V₂ p₂

Valᵍ-≐ˢ {St} {St'} es ([ ρ ]ᵍ G) V f {St''} (read e rel)
  with grad-typ⇒var V
... | _ , c , g , refl with replay (≐ˢ-sym es) e
...   | St₂ , e₀ , es₂ , h rewrite castᵛ-var (toCtx-≐ˢ es) g c =
  Valᵍ-≡ᵛ G ((sym (lookup-body-≡ St'' cellEq rel rel₀)))
    (Valᵍ-≡ᵛ G (sym bridge)
      (Valᵍ-≐ˢ (≐ˢ-sym es₂) G _ (f (read e₀ rel₀))))
  where
    cellEq = ≤ₛ-embed-≐ˢ es es₂ h c
    rel₀   = subst (_≾ᵣ ρ) (cong proj₁ cellEq) rel

    bridge =
      trans
        (lookup-body-≐ˢ es₂ (Var-cast (sym (toCtx-≐ˢ es₂)) (≤ₛ-embed e₀ c))
                        (≤ₛ-embed e₀ c) refl rel₀ rel₀)
        ((castᵛ-irr (sym (toCtx-≐ˢ es₂)) (toCtx-≐ˢ (≐ˢ-sym es₂)) _))

-- COMPUTATIONS ACROSS THE STATE EQUIVALENCE
--
-- One lemma carrying *both* relations: the states' and the terms'. They cannot
-- be separated — the `comp-op` case replays the resumption's reach and recurses,
-- and the two continuations come out of `cast-perform⁻` related only by `_≡_`.
--
-- Parameterised by the value predicate's transport rather than mutual with
-- `Val-≐ˢ`, so that both recurse structurally on the *type*.


-- The reduct a resumption builds, compared across the two states.

resume-≐ˢ : ∀ {A B ε ρ} {St St' St₂ St₂' : 𝕊 []}
         → (es : St ≐ˢ St') → (es₂ : St₂ ≐ˢ St₂')
         → {q : St ⊑ₛ[ ρ ] St₂} → {q' : St' ⊑ₛ[ ρ ] St₂'}
         → ext q ≤≐ ext q'
         → {M : toCtx St ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε}
         → {M' : toCtx St' ⟨ ρ ⟩ ∷ B ⊢C⦂ A ‼ ε}
         → M ≡ castᶜ (cong (λ Γ₀ → Γ₀ ⟨ ρ ⟩ ∷ B) (sym (toCtx-≐ˢ es))) M'
         → {W : toCtx St₂ ⊢V⦂ B} → {W' : toCtx St₂' ⊢V⦂ B}
         → W ≡ castᵛ (sym (toCtx-≐ˢ es₂)) W'
         -------------------------------------------------------------------
         → resume q M W
         ≡ castᶜ (sym (toCtx-≐ˢ es₂)) (resume q' M' W')

resume-≐ˢ {A} {B} {ρ = ρ} es es₂ {q} {q'} h {M} {M'} eM {W} {W'} eW =
  trans
    (sub-≡ᶜ split-[] eW
      (trans (C-rename-≡ (cong-∷-ren-≐ʳ (unbox-ren-≐ˢ es es₂ h)) M)
                (C-rename-cong (cong-∷-ren _)
                  (subst (λ z → M ≡ z)
                         (castᶜ-irr (cong (λ Γ₀ → Γ₀ ⟨ ρ ⟩ ∷ B)
                                          (sym (toCtx-≐ˢ es)))
                                    (cong (_∷ B) e₁) M')
                         eM))))
    ((trans (cong (λ z → z [ split-[] ↦ castᵛ e₂ W' ]c)
                       (cast-rename-∷ e₁ e₂ (unbox-ren q') M'))
                 (cast-app-reduct e₂ (C-rename (cong-∷-ren (unbox-ren q')) M') W')))
  where
    e₁ = cong (_⟨ ρ ⟩) (sym (toCtx-≐ˢ es))
    e₂ = sym (toCtx-≐ˢ es₂)

Comp-≐ˢ : ∀ {A P ε} {St St' : 𝕊 []} → (es : St ≐ˢ St')
       → (tr : ∀ {St₁ St₁' : 𝕊 []} → (es₁ : St₁ ≐ˢ St₁')
             → (V : toCtx St₁ ⊢V⦂ A) → P St₁ V
             → P St₁' (castᵛ (toCtx-≐ˢ es₁) V))
       → (tr≐ : ∀ {St₁ : 𝕊 []} {V V' : toCtx St₁ ⊢V⦂ A}
              → V ≡ V' → P St₁ V → P St₁ V')
       → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε}
       → M ≡ castᶜ (sym (toCtx-≐ˢ es)) M'
       -------------------------------------------------------------
       → Comp A P ε St M → Comp A P ε St' M'

Comp-≐ˢ es tr tr≐ eM (comp-ret rs pV) with ↝*-≐ˢ es eM rs
... | St₁' , N' , es₁ , rs' , eN with cast-return⁻ (sym (toCtx-≐ˢ es₁)) N' eN
...   | V' , refl , eV =
  comp-ret rs'
    (tr≐ (subst (λ z → castᵛ (toCtx-≐ˢ es₁) _ ≡ z)
                (castᵛ-castᵛ (sym (toCtx-≐ˢ es₁)) (toCtx-≐ˢ es₁) V')
                (castᵛ-≡ (toCtx-≐ˢ es₁) eV))
         (tr es₁ _ pV))

Comp-≐ˢ {A} {P} es tr tr≐ eM (comp-op {op = op} {M' = Mk} rs pW pk)
  with ↝*-≐ˢ es eM rs
... | St₁' , N' , es₁ , rs' , eN with cast-perform⁻ (sym (toCtx-≐ˢ es₁)) N' eN
...   | W' , Mk' , refl , eW , eMk =
  comp-op rs'
    (Valᵍ-≡ᵛ (param op)
      (subst (λ z → castᵛ (toCtx-≐ˢ es₁) _ ≡ z)
             (castᵛ-castᵛ (sym (toCtx-≐ˢ es₁)) (toCtx-≐ˢ es₁) W')
             (castᵛ-≡ (toCtx-≐ˢ es₁) eW))
      (Valᵍ-≐ˢ es₁ (param op) _ pW))
    (λ q' W'' pW'' → step q' W'' pW'')
  where
    ρ = mapᵉ (op-grade op)

    step : ∀ {St₂ : 𝕊 []} → (q' : _ ⊑ₛ[ ρ ] St₂)
         → (W'' : toCtx St₂ ⊢V⦂ type-of-gtype (arity op))
         → Valᵍ (arity op) St₂ W''
         → Comp A P _ St₂ (resume q' Mk' W'')
    step {St₂} q' W'' pW'' with reach-replay (≐ˢ-sym es₁) q'
    ... | St₃ , q , es₃ , h =
      Comp-≐ˢ (≐ˢ-sym es₃) tr tr≐
        (resume-≐ˢ es₁ (≐ˢ-sym es₃) (≤≐-sym h) eMk
          (subst (λ z → castᵛ (toCtx-≐ˢ es₃) W'' ≡ z)
                 (castᵛ-irr (toCtx-≐ˢ es₃)
                            (sym (toCtx-≐ˢ (≐ˢ-sym es₃))) W'')
                 (refl)))
        (pk q (castᵛ (toCtx-≐ˢ es₃) W'')
             (Valᵍ-≐ˢ es₃ (arity op) W'' pW''))

-- VALUES ACROSS THE STATE EQUIVALENCE
--
-- Recursion on the type. Both Kripke clauses replay the other state's extension
-- and transport back; the arrow clause is where `Comp-≐ˢ` is called, at the
-- smaller type `B`, which is what keeps the two definitions non-mutual.

Val-≐ˢ : ∀ {St St' : 𝕊 []} → (es : St ≐ˢ St') → (A : VType)
       → (V : toCtx St ⊢V⦂ A)
       → Val A St V → Val A St' (castᵛ (toCtx-≐ˢ es) V)

Val-≐ˢ es (Base b)  V p = tt
Val-≐ˢ es Unit      V p = tt
Val-≐ˢ es Empty     V p = tt
Val-≐ˢ es (A |×| B) .(⦉ V₁ , V₂ ⦊) (V₁ , V₂ , refl , p₁ , p₂) =
  _ , _ , cast-pair (toCtx-≐ˢ es) {V₁} {V₂}
  , Val-≐ˢ es A V₁ p₁ , Val-≐ˢ es B V₂ p₂

Val-≐ˢ {St} {St'} es (A ⇒ (B ‼ ε)) .(lam M) (M , refl , f) =
    _ , cast-lam (toCtx-≐ˢ es) M
  , λ {St''} q' M₂ eM₂ W pW → step q' M₂ eM₂ W pW
  where
    e = toCtx-≐ˢ es

    step : ∀ {St'' : 𝕊 []} → (q' : St' ⊑ₛ[ uᵣ ] St'')
         → (M₂ : toCtx St'' ∷ A ⊢C⦂ B ‼ ε)
         → M₂ ≡ reach-under q' (castᶜ (cong (_∷ A) e) M)
         → (W : toCtx St'' ⊢V⦂ A) → Val A St'' W
         → Comp B (Val B) ε St'' (M₂ [ split-[] ↦ W ]c)
    step {St''} q' M₂ eM₂ W pW with reach-replay (≐ˢ-sym es) q'
    ... | St₂ , q , es₂ , h =
      Comp-≐ˢ (≐ˢ-sym es₂) (λ es₁ V₀ → Val-≐ˢ es₁ B V₀) (Val-≡ᵛ B)
        ((trans (cast-app-reduct e₂ M₂ W)
                     (castᶜ-irr e₂ (sym (toCtx-≐ˢ (≐ˢ-sym es₂)))
                                (M₂ [ split-[] ↦ W ]c))))
        (f q (castᶜ (cong (_∷ A) e₂) M₂) eM₃ (castᵛ e₂ W)
             (Val-≐ˢ es₂ A W pW))
      where
        e₂ = toCtx-≐ˢ es₂

        eM₃ : castᶜ (cong (_∷ A) e₂) M₂ ≡ reach-under q M
        eM₃ =
          trans (castᶜ-≡ (cong (_∷ A) e₂) eM₂)
            (trans
              ((sym (cast-rename-∷ (sym e) e₂ (reach-renᵘ q')
                                        (castᶜ (cong (_∷ A) e) M))))
              (trans
                ((cong (C-rename
                              (cong-∷-ren (castʳ² (sym e) e₂ (reach-renᵘ q'))))
                            (castᶜ-castᶜ (cong (_∷ A) e) (cong (_∷ A) (sym e)) M)))
                (sym
                  (C-rename-≡
                    (cong-∷-ren-≐ʳ
                      (≐ʳ-trans (reach-renᵘ-≐ˢ es (≐ˢ-sym es₂) (≤≐-sym h))
                                (castʳ²-irr (sym e) (sym e)
                                            (sym (toCtx-≐ˢ (≐ˢ-sym es₂))) e₂
                                            (reach-renᵘ q'))))
                    M))))

Val-≐ˢ {St} {St'} es ([ ρ ] A) V f {St''} (read e rel)
  with grad-typ⇒var V
... | _ , c , g , refl with replay (≐ˢ-sym es) e
...   | St₂ , e₀ , es₂ , h rewrite castᵛ-var (toCtx-≐ˢ es) g c =
  Val-≡ᵛ A ((sym (lookup-body-≡ St'' cellEq rel rel₀)))
    (Val-≡ᵛ A (sym bridge)
      (Val-≐ˢ (≐ˢ-sym es₂) A _ (f (read e₀ rel₀))))
  where
    cellEq = ≤ₛ-embed-≐ˢ es es₂ h c
    rel₀   = subst (_≾ᵣ ρ) (cong proj₁ cellEq) rel

    bridge =
      trans
        (lookup-body-≐ˢ es₂ (Var-cast (sym (toCtx-≐ˢ es₂)) (≤ₛ-embed e₀ c))
                        (≤ₛ-embed e₀ c) refl rel₀ rel₀)
        ((castᵛ-irr (sym (toCtx-≐ˢ es₂)) (toCtx-≐ˢ (≐ˢ-sym es₂)) _))

-- Hence reducibility is insensitive to the term equivalence: the special case
-- `es := ≐ˢ-refl St`, where `toCtx-≐ˢ-refl` makes the cast the identity.

Comp-≡ᶜ : ∀ {A ε} {St : 𝕊 []} {M M' : toCtx St ⊢C⦂ A ‼ ε}
        → M ≡ M' → Comp' A ε St M → Comp' A ε St M'
Comp-≡ᶜ {A} {ε} {St} {M} {M'} eM pM =
  Comp-≐ˢ (≐ˢ-refl St) (λ es₁ V₀ → Val-≐ˢ es₁ A V₀) (Val-≡ᵛ A)
    (subst (λ z → M ≡ castᶜ (sym z) M') (sym (toCtx-≐ˢ-refl St)) eM)
    pM

-- Handling is `Adequacy.Handle`, above `Environment`: as sequencing, plus a
-- clause premise, and needing `sub-wk-C` for the same reason.

-- The freshly allocated cell is reducible: a reach out of `St ∷ₛ V` at `ρ` is
-- one out of `St` (the allocation accumulates nothing), and reading the cell
-- back returns the stored value. Which cell is read is settled — `unbox-ren-img`
-- sends it to `≤ₛ-embed (ext q) Hd` — and what it holds is settled too, by
-- `≤ₛ-embed-fst`/`≤ₛ-embed-lookup`: the cell is split off at `St` and holds `V`,
-- however far the state has grown.
--
-- What is left is one renaming agreement, `GradedReach.alloc-lookup-≡`: the
-- two renamings both push the value's context under everything the state has
-- gained since, the lookup by `wk-ren-⟨ρ⟩-ctx` and the reach by `≤ₛ-embed`.

store-fresh : ∀ {A ρ} {St : 𝕊 []} → (V : ([] ++ᶜ toCtx St ⟨ ρ ⟩) ⊢V⦂ A)
            → (∀ {St'} → (q : St ⊑ₛ[ ρ ] St')
                 → Val A St' (V-rename (eq-ren ++ᶜ-identityˡ ∘ʳ unbox-ren q) V))
            → (f : ¬ Eternal ([ ρ ] A) → uᵣ ≾ᵣ uᵣ)
            ------------------------------------------
            → Val ([ ρ ] A) (St ∷ₛ V) (var f Hd)

store-fresh {A} {ρ} {St} V pV f {St'} r =
  Val-≡ᵛ A (sym (alloc-lookup-≡ V (extᶜ r) (ready r) q₀ refl)) (pV q₀)
  where
    e   = extᶜ r
    rel = ready r
    -- the allocation accumulates nothing, so the cell's readability at `St'`
    -- *is* the bound the reach back to `St` needs
    q₀ : St ⊑ₛ[ ρ ] St'
    q₀ = reach (≤ₛ-trans (∷-suc V id-suc) e)
               (≾ᵣ-trans
                 (≾ᵣ-reflexive
                   (trans (≤ₛ-grade-trans (∷-suc V id-suc) e)
                          (sym (≤ₛ-embed-grade e (Hd {Γ = toCtx St})))))
                 rel)

-- THE STORE ON VARIABLES
--
-- Every variable of a state context is of box type, so at the other four types
-- there is nothing to show (`⊤`, or no such variable at all). At a box type a
-- *usable* variable — one carrying the grade bound `var` demands — is
-- reducible, and that is the store read at the later states its own box grade
-- allows: `unbox-ren-img` identifies the cell the lookup names with
-- `≤ₛ-embed (ext q)`, which is exactly where the store speaks. So `Val` at a
-- box type is not a second assumption about the state; it is this one.

store-var : ∀ {A ρ} {St : 𝕊 []} → Store St
          → (x : A ∈[ ρ ] toCtx St) → (f : ¬ Eternal A → ρ ≾ᵣ uᵣ)
          --------------------------------------------------------
          → Val A St (var f x)

store-var {Base b}    pSt x f = tt
store-var {Unit}      pSt x f = tt
store-var {Empty}     pSt x f = tt
store-var {A₁ |×| A₂} pSt x f = ⊥-elim (⦉⦊-not-in-toCtx x)
store-var {A₁ ⇒ C}    pSt x f = ⊥-elim (⇒-not-in-toCtx x)

store-var {[ ρ ] A} pSt x f r = pSt x r
