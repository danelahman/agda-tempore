------------------------------------------------------------------------
-- The model-side interface: head faithfulness.                         --
--                                                                    --
-- Adequacy does not need *exhaustiveness* ("every point of `Tᵒ A ε` has --
-- a weak-head form") — the machine supplies the shape and `↝*-sound`    --
-- transports it. What the model has to provide is that it does not      --
-- identify distinct heads: no-confusion and injectivity.                --
--                                                                    --
-- Both are stated at the composite shape `↝*-sound` produces: a head    --
-- (`ηᵀ`-leaf or `opᵀ`-node) bound after a run's *time transition*.       --
-- Transitions are not arbitrary morphisms — a stuck one observes nothing --
-- — so they are restricted to the class `stepsᵀ` builds, which also      --
-- carries the run's tick total.                                        --
--                                                                    --
-- For the presheaf model these are facts about the tree setoid `_≈ᵗ_`,   --
-- proved by induction on its derivations (`sub-*`, `delay-zero`,        --
-- `delay-plus`, `≈ᵗ-sym`, `≈ᵗ-trans`) against a head observation        --
-- indexed by a path of `⊑`-witnesses. See `notes/adequacy-plan.md`.      --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

open import DenotationalSemantics.Model.Category
open import DenotationalSemantics.Model.Modality.Future
open import DenotationalSemantics.Model.Modality.Past
open import DenotationalSemantics.Model.Modality.Adjunction
open import DenotationalSemantics.Model.GroundTypes
open import DenotationalSemantics.Model.GroundEternal
open import DenotationalSemantics.Model.Monad

module OperationalSemantics.Adequacy.HeadFaithful
         (Spec : LanguageSpec)
         (Cat : Category)
         (Fut : Future Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (Pst : Past Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)))
         (Adj : Adjunction Cat (GradeSystem.RGrade (LanguageSpec.Grades Spec)) Fut Pst)
         (GTy : GroundTypes Spec Cat Fut)
         (Mon : Monad Spec Cat Fut Pst Adj GTy)
         (GE : GroundEternal Spec Cat Fut Pst Adj GTy)
       where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import Syntax.Contexts Spec
open import Syntax.Language Spec
open import Syntax.Types    Spec

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open Category Cat
open Future Fut using ([_]ᵒ; [_]ᶠ)
open Past Pst using (⟨_⟩ᵒ; ⟨_⟩ᶠ)
open Adjunction Adj using (η⊣)
open GroundTypes GTy using (⟦_⟧ᵍ; ⟦_⟧ᵇ; ⟦_⟧ᵇᶜ)
open Monad Mon

open import DenotationalSemantics.Interpretation.Types    Spec Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Contexts Spec Cat Fut Pst Adj GTy Mon
open import DenotationalSemantics.Interpretation.Terms    Spec Cat Fut Pst Adj GTy Mon GE
open import DenotationalSemantics.Interpretation.State    Spec Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Soundness.Preservation   Spec Cat Fut Pst Adj GTy Mon GE

open import OperationalSemantics.Adequacy.Evaluation Spec

-- A RUN'S TIME TRANSITION
--
-- The class of morphisms `stepsᵀ` builds: `ηᵀ`, and a `DELAY`'s tick bound
-- into a further transition. The index is the tick total, the run's observable
-- time. Closed under morphism equality, since transitions are only ever used
-- up to `_≈ᵐ_`.

data Delaysᵐ : ∀ {X Y : Obj} {δ : E} → (X →ᵐ Tᵒ Y δ) → ℕ → Set₁ where

  no-delay   : ∀ {X : Obj}
             --------------------
             → Delaysᵐ (ηᵀ {X}) 0

  η-step     : ∀ {X Y : Obj} {δ : E} {n : ℕ} {t : X →ᵐ Tᵒ Y δ}
             → Delaysᵐ t n
             ---------------------
             → Delaysᵐ (t ⋄ ηᵀ) n

  τ-step     : ∀ {X Z : Obj} {δ : E} {n : ℕ}
             → (τ : ℕ) → {t : ⟨ of-natʳ τ ⟩ᵒ X →ᵐ Tᵒ Z δ}
             → Delaysᵐ t n
             ----------------------------------------------------------------
             → Delaysᵐ (t ⋄ (delayᵀ τ ∘ᵐ [ of-natʳ τ ]ᶠ ηᵀ ∘ᵐ η⊣)) (τ + n)

  delays-≈   : ∀ {X Y : Obj} {δ : E} {n : ℕ} {t t' : X →ᵐ Tᵒ Y δ}
             → t ≈ᵐ t' → Delaysᵐ t n
             -----------------------
             → Delaysᵐ t' n

-- A run's transition is one of the class above, and its index is the run's
-- tick total: the bridge between the syntactic observable (`ticks`) and the
-- model-side interface. Step by step, since `stepᵀ` is `ηᵀ` for every rule but
-- `DELAY`, and both `stepᵀ` and `step-ticks` recurse identically through the
-- two congruences.

step-delays : ∀ {ε ε' n} {St St' : 𝕊 []} {A : VType}
            → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
            → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩)
            → {X : Obj} → {δ : E} → {t : ⟦ hist St' ⟧ᶜᵗˣ →ᵐ Tᵒ X δ}
            → Delaysᵐ t n
            ------------------------------------------
            → Delaysᵐ (t ⋄ stepᵀ r) (step-ticks r + n)

step-delays APP                d = η-step d
step-delays MATCH              d = η-step d
step-delays (SEQ-STEP r _)     d = step-delays r d
step-delays SEQ-RET            d = η-step d
step-delays SEQ-OP             d = η-step d
step-delays (DELAY {τ = τ})    d = τ-step τ d
step-delays HANDLE-RET         d = η-step d
step-delays (HANDLE-STEP r _)  d = step-delays r d
step-delays HANDLE-OP          d = η-step d
step-delays BOX                d = η-step d
step-delays UNBOX              d = η-step d
step-delays COERCE             d = η-step d

stepsᵀ-delays : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
              → (rs : cf ↝* cf')
              ------------------------------
              → Delaysᵐ (stepsᵀ rs) (ticks rs)

stepsᵀ-delays ε*       = no-delay
stepsᵀ-delays (r ◅ rs) = step-delays r (stepsᵀ-delays rs)

-- THE TWO HEAD SHAPES, as morphisms
--
-- `⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ` is a leaf and `⟦ ⟨ St , perform op W M' ⟩ ⟧ᶜᶠ` an
-- operation node (`whnf-shape` below).

leafᵐ : ∀ {X Y : Obj} → (a : Y →ᵐ X) → Y →ᵐ Tᵒ X uₑ
leafᵐ a = ηᵀ ∘ᵐ a

nodeᵐ : ∀ {X Y : Obj} {ε : E} → (op : Op)
      → (w : Y →ᵐ ⟦ param op ⟧ᵍ)
      → (k : Y →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ X ε))
      → Y →ᵐ Tᵒ X (op-grade op ·ₑ ε)
nodeᵐ op w k = opᵀ op ∘ᵐ ⟨ w , k ⟩ᵐ

-- A head, run after a transition and coerced back to the source's grade: the
-- right-hand side of `↝*-sound`.

delayedᵐ : ∀ {X Y : Obj} {ε ε' δ : E}
         → (h : Y →ᵐ Tᵒ X ε') → (d : 𝟙ᵐ →ᵐ Tᵒ Y δ) → δ ·ₑ ε' ≾ₑ ε
         → 𝟙ᵐ →ᵐ Tᵒ X ε
delayedᵐ {Y = Y} {δ = δ} h d r = T-≤ r ∘ᵐ _⋄_ {𝟙ᵐ} {Y} h d

------------------------------------------------------------------------
-- THE INTERFACE
------------------------------------------------------------------------

-- No-confusion and injectivity at the head. A model that satisfies this
-- reflects the shape of a whnf; the presheaf model does, by the `Head`
-- observation on trees.

record HeadFaithful : Set₂ where

  field

    -- A delayed leaf is never a delayed operation node.

    ret≢op : ∀ {X Y₁ Y₂ : Obj} {ε ε₂ δ₁ δ₂ : E} {n₁ n₂ : ℕ} {op : Op}
           → {a : Y₁ →ᵐ X}
           → {w : Y₂ →ᵐ ⟦ param op ⟧ᵍ}
           → {k : Y₂ →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ X ε₂)}
           → {d₁ : 𝟙ᵐ →ᵐ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
           → {d₂ : 𝟙ᵐ →ᵐ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
           → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
           → (r₂ : δ₂ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
           ------------------------------------------------------------------
           → ¬ (delayedᵐ (leafᵐ a) d₁ r₁ ≈ᵐ delayedᵐ (nodeᵐ op w k) d₂ r₂)

    -- Distinct operations are distinct nodes.

    op-inj : ∀ {X Y₁ Y₂ : Obj} {ε ε₁ ε₂ δ₁ δ₂ : E} {n₁ n₂ : ℕ} {op₁ op₂ : Op}
           → {w₁ : Y₁ →ᵐ ⟦ param op₁ ⟧ᵍ}
           → {k₁ : Y₁ →ᵐ [ mapᵉ (op-grade op₁) ]ᵒ (⟦ arity op₁ ⟧ᵍ ⇒ᵐ Tᵒ X ε₁)}
           → {w₂ : Y₂ →ᵐ ⟦ param op₂ ⟧ᵍ}
           → {k₂ : Y₂ →ᵐ [ mapᵉ (op-grade op₂) ]ᵒ (⟦ arity op₂ ⟧ᵍ ⇒ᵐ Tᵒ X ε₂)}
           → {d₁ : 𝟙ᵐ →ᵐ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
           → {d₂ : 𝟙ᵐ →ᵐ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
           → (r₁ : δ₁ ·ₑ (op-grade op₁ ·ₑ ε₁) ≾ₑ ε)
           → (r₂ : δ₂ ·ₑ (op-grade op₂ ·ₑ ε₂) ≾ₑ ε)
           → delayedᵐ (nodeᵐ op₁ w₁ k₁) d₁ r₁ ≈ᵐ delayedᵐ (nodeᵐ op₂ w₂ k₂) d₂ r₂
           -----------------------------------------------------------------------
           → op₁ ≡ op₂

    -- Constant leaves are injective: what makes the returned answer at base
    -- type observable. (A constant's denotation factors through `𝟙ᵐ`, which is
    -- what makes this statement independent of the two histories.)

    leaf-const : ∀ {Y₁ Y₂ : Obj} {b : BaseType} {ε δ₁ δ₂ : E} {n₁ n₂ : ℕ}
               → {c₁ c₂ : BaseConstants b}
               → {d₁ : 𝟙ᵐ →ᵐ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
               → {d₂ : 𝟙ᵐ →ᵐ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
               → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
               → (r₂ : δ₂ ·ₑ uₑ ≾ₑ ε)
               → delayedᵐ (leafᵐ (⟦ c₁ ⟧ᵇᶜ ∘ᵐ terminalᵐ)) d₁ r₁
               ≈ᵐ delayedᵐ (leafᵐ (⟦ c₂ ⟧ᵇᶜ ∘ᵐ terminalᵐ)) d₂ r₂
               -----------------------------------------------------------
               → ⟦ c₁ ⟧ᵇᶜ ≈ᵐ ⟦ c₂ ⟧ᵇᶜ

-- The timed refinement: the tick total is observable too. Split off, because
-- the natural proof needs the Kripke frame to *interpolate* a composite step
-- (`delay-plus` in the other direction), which fails in general — see
-- `notes/pra-and-unbox.md`.

record HeadTimed : Set₂ where

  field

    ret-ticks-eq : ∀ {X Y₁ Y₂ : Obj} {ε δ₁ δ₂ : E} {n₁ n₂ : ℕ}
                 → {a₁ : Y₁ →ᵐ X} → {a₂ : Y₂ →ᵐ X}
                 → {d₁ : 𝟙ᵐ →ᵐ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
                 → {d₂ : 𝟙ᵐ →ᵐ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
                 → (r₁ : δ₁ ·ₑ uₑ ≾ₑ ε)
                 → (r₂ : δ₂ ·ₑ uₑ ≾ₑ ε)
                 → delayedᵐ (leafᵐ a₁) d₁ r₁ ≈ᵐ delayedᵐ (leafᵐ a₂) d₂ r₂
                 ---------------------------------------------------------
                 → n₁ ≡ n₂

    op-ticks-eq : ∀ {X Y₁ Y₂ : Obj} {ε ε₁ ε₂ δ₁ δ₂ : E} {n₁ n₂ : ℕ} {op : Op}
                → {w₁ : Y₁ →ᵐ ⟦ param op ⟧ᵍ}
                → {k₁ : Y₁ →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ X ε₁)}
                → {w₂ : Y₂ →ᵐ ⟦ param op ⟧ᵍ}
                → {k₂ : Y₂ →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ X ε₂)}
                → {d₁ : 𝟙ᵐ →ᵐ Tᵒ Y₁ δ₁} → Delaysᵐ d₁ n₁
                → {d₂ : 𝟙ᵐ →ᵐ Tᵒ Y₂ δ₂} → Delaysᵐ d₂ n₂
                → (r₁ : δ₁ ·ₑ (op-grade op ·ₑ ε₁) ≾ₑ ε)
                → (r₂ : δ₂ ·ₑ (op-grade op ·ₑ ε₂) ≾ₑ ε)
                → delayedᵐ (nodeᵐ op w₁ k₁) d₁ r₁ ≈ᵐ delayedᵐ (nodeᵐ op w₂ k₂) d₂ r₂
                ---------------------------------------------------------------------
                → n₁ ≡ n₂

-- Faithfulness of the base-constant interpretation: an assumption on the
-- `GroundTypes` parameter, not a theorem. (Definability — every semantic
-- element being some `⟦ V ⟧` — is *not* needed: the adequacy statement
-- compares two programs, so injectivity suffices.)

record BaseFaithful : Set where

  field

    const-inj : ∀ {b : BaseType} {c₁ c₂ : BaseConstants b}
              → ⟦ c₁ ⟧ᵇᶜ ≈ᵐ ⟦ c₂ ⟧ᵇᶜ
              ----------------------
              → c₁ ≡ c₂

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- Uniformity of the handlers a run reaches is now carried by the term's own
  -- certificate, so `Uniform↝*` is inhabited outright (every case is `⊤`).

  uniform↝* : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
            → (rs : cf ↝* cf') → (p : Paramᶜᶠ cf)
            ------------------------------------
            → Uniform↝* rs p

  -- A whnf configuration denotes a head: a `return` is a leaf, a `perform` an
  -- operation node. Unfolding `⟦_⟧ᶜᵗ` at the two whnf formers, with the
  -- `ty-gty` adapters absorbed.

  ret-whnf-shape : ∀ {A} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ A)
                 → (pSt : Paramˢ St) → (pV : Paramᵛ V)
                 → Σ[ a ∈ (⟦ hist St ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ) ]
                     ⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV) ≈ᵐ leafᵐ a

  op-whnf-shape : ∀ {A ε} {St : 𝕊 []} {op : Op}
                → (W : toCtx St ⊢V⦂ type-of-gtype (param op))
                → (M' : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                          ⊢C⦂ A ‼ ε)
                → (pSt : Paramˢ St) → (pW : Paramᵛ W) → (pM' : Paramᶜ M')
                → Σ[ w ∈ (⟦ hist St ⟧ᶜᵗˣ →ᵐ ⟦ param op ⟧ᵍ) ]
                  Σ[ k ∈ (⟦ hist St ⟧ᶜᵗˣ
                            →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε)) ]
                     ⟦ ⟨ St , perform op W M' ⟩ ⟧ᶜᶠ (pSt , pW , pM') ≈ᵐ nodeᵐ op w k

  -- A base-typed value's leaf is a constant's: `base-canonical` transported to
  -- the model, where `⟦ const c ⟧ᵛᵗ = ⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ`.

  base-leaf-const : ∀ {b} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ Base b)
                  → (pSt : Paramˢ St) → (pV : Paramᵛ V)
                  → Σ[ c ∈ BaseConstants b ]
                      ⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                        ≈ᵐ leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ)
