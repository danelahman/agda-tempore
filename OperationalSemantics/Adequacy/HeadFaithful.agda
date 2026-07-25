------------------------------------------------------------------------
-- The model-side interface: head faithfulness.                       --
--                                                                    --
-- The model must not identify distinct heads: no-confusion and       --
-- injectivity, at the composite shape `↝*-sound` produces — a head   --
-- (`ηᵀ`-leaf or `opᵀ`-node) bound after a run's time transition.     --
-- Transitions are restricted to the class `stepsᵀ` builds, which     --
-- carries the run's tick total.                                      --
--                                                                    --
-- For the presheaf model these are facts about the tree setoid       --
-- `_≈ᵗ_`, proved by induction on its derivations against a head      --
-- observation.                                                       --
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
-- into a further transition, indexed by the tick total. Closed under `_≈ᵐ_`.

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

-- A run's transition lies in that class, at the run's tick total: the bridge
-- between the syntactic observable (`ticks`) and the model-side interface.
-- `stepᵀ` is `ηᵀ` for every rule but `DELAY`.

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

-- The head is the only part a `delayedᵐ` shape is congruent in that the
-- statements below need.

delayedᵐ-cong : ∀ {X Y : Obj} {ε ε' δ : E} {h h' : Y →ᵐ Tᵒ X ε'}
              → (d : 𝟙ᵐ →ᵐ Tᵒ Y δ) → (r : δ ·ₑ ε' ≾ₑ ε)
              → h ≈ᵐ h'
              ---------------------------------------
              → delayedᵐ h d r ≈ᵐ delayedᵐ h' d r
delayedᵐ-cong d r eh = ∘ᵐ-congʳ (∘ᵐ-congʳ (∘ᵐ-congˡ (T-congᶠ eh)))

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

-- The timed refinement: the tick total is observable too. Split off because
-- proving it needs the Kripke frame to interpolate a composite step, which
-- holds only for coarse-unit frames (`notes/pra-and-unbox.md`).

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
-- `GroundTypes` parameter, not a theorem.

record BaseFaithful : Set where

  field

    const-inj : ∀ {b : BaseType} {c₁ c₂ : BaseConstants b}
              → ⟦ c₁ ⟧ᵇᶜ ≈ᵐ ⟦ c₂ ⟧ᵇᶜ
              ----------------------
              → c₁ ≡ c₂

-- UNIFORMITY IS FREE
--
-- Handler uniformity is carried by the term's own certificate, so
-- `Uniform↝`/`Uniform↝*` are `⊤` in every case.

uniform↝ : ∀ {A ε ε'} {St St' : 𝕊 []}
         → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ A ‼ ε'}
         → (r : ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩) → (pM : Paramᶜ M)
         ---------------------------------------------------
         → Uniform↝ r pM

uniform↝ APP                 _         = tt
uniform↝ MATCH               _         = tt
uniform↝ (SEQ-STEP r _)      (pM , _)  = uniform↝ r pM
uniform↝ SEQ-RET             _         = tt
uniform↝ SEQ-OP              _         = tt
uniform↝ DELAY               _         = tt
uniform↝ HANDLE-RET          _         = tt
uniform↝ (HANDLE-STEP r _)   (pM , _)  = uniform↝ r pM
uniform↝ HANDLE-OP           _         = tt
uniform↝ BOX                 _         = tt
uniform↝ UNBOX               _         = tt
uniform↝ COERCE              _         = tt

uniform↝* : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
          → (rs : cf ↝* cf') → (p : Paramᶜᶠ cf)
          ------------------------------------
          → Uniform↝* rs p

uniform↝* ε*       p          = tt
uniform↝* (r ◅ rs) (pS , pM)  =
  uniform↝ r pM , uniform↝* rs (stepᴾᶜᶠ r (pS , pM))

-- WHNF CONFIGURATIONS DENOTE HEADS
--
-- Unfold `⟦_⟧ᶜᵗ` at the two whnf formers and push the state's environment
-- inside; it survives only inside the head's components.

ret-whnf-shape : ∀ {A} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ A)
               → (pSt : Paramˢ St) → (pV : Paramᵛ V)
               → Σ[ a ∈ (⟦ hist St ⟧ᶜᵗˣ →ᵐ ⟦ A ⟧ᵛ) ]
                   ⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV) ≈ᵐ leafᵐ a

ret-whnf-shape {St = St} V pSt pV =
  ⟦ V ⟧ᵛᵗ pV ∘ᵐ ⟦ St ⟧ˢ pSt , ∘ᵐ-assoc ηᵀ (⟦ V ⟧ᵛᵗ pV) (⟦ St ⟧ˢ pSt)

op-whnf-shape : ∀ {A ε} {St : 𝕊 []} {op : Op}
              → (W : toCtx St ⊢V⦂ type-of-gtype (param op))
              → (M' : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                        ⊢C⦂ A ‼ ε)
              → (pSt : Paramˢ St) → (pW : Paramᵛ W) → (pM' : Paramᶜ M')
              → Σ[ w ∈ (⟦ hist St ⟧ᶜᵗˣ →ᵐ ⟦ param op ⟧ᵍ) ]
                Σ[ k ∈ (⟦ hist St ⟧ᶜᵗˣ
                          →ᵐ [ mapᵉ (op-grade op) ]ᵒ (⟦ arity op ⟧ᵍ ⇒ᵐ Tᵒ ⟦ A ⟧ᵛ ε)) ]
                   ⟦ ⟨ St , perform op W M' ⟩ ⟧ᶜᶠ (pSt , pW , pM') ≈ᵐ nodeᵐ op w k

op-whnf-shape {St = St} {op = op} W M' pSt pW pM' =
    _ , _
  , ≈ᵐ-trans (∘ᵐ-assoc (opᵀ op) _ (⟦ St ⟧ˢ pSt))
             (∘ᵐ-congʳ (⟨⟩ᵐ-∘ _ _ (⟦ St ⟧ˢ pSt)))

-- A base-typed value's leaf is a constant's (`base-canonical`); the state's
-- environment is absorbed by the terminal object.

base-leaf-const : ∀ {b} {St : 𝕊 []} → (V : toCtx St ⊢V⦂ Base b)
                → (pSt : Paramˢ St) → (pV : Paramᵛ V)
                → Σ[ c ∈ BaseConstants b ]
                    (V ≡ const c)
                  × (⟦ ⟨ St , return V ⟩ ⟧ᶜᶠ (pSt , pV)
                       ≈ᵐ leafᵐ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ))

base-leaf-const {St = St} V pSt pV with base-canonical V
base-leaf-const {St = St} .(const c) pSt pV | c , refl =
    c , refl
  , ≈ᵐ-trans (∘ᵐ-assoc ηᵀ (⟦ c ⟧ᵇᶜ ∘ᵐ terminalᵐ) (⟦ St ⟧ˢ pSt))
      (∘ᵐ-congʳ (≈ᵐ-trans (∘ᵐ-assoc ⟦ c ⟧ᵇᶜ terminalᵐ (⟦ St ⟧ˢ pSt))
                          (∘ᵐ-congʳ terminalᵐ-unique)))
