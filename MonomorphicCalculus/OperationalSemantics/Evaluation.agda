------------------------------------------------------------------------
-- Halting: a run to a finished computation.                          --
--                                                                    --
-- A configuration halts when it runs to a returned value or to an    --
-- unhandled operation call (`Halts`, `Final`). What is observed of   --
-- a halting is how it finished (`outcome`) and the run's tick total  --
-- (`halt-ticks`). Reduction is deterministic (`⟶-det`), so a         --
-- configuration halts in one way only (`halts-det`).                 --
--                                                                    --
-- Syntactic: no model parameters.                                    --
------------------------------------------------------------------------

import Data.Bool.Base as Bool
open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module MonomorphicCalculus.OperationalSemantics.Evaluation (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import MonomorphicCalculus.OperationalSemantics.Reduction           Spec
open import MonomorphicCalculus.OperationalSemantics.State               Spec
open import MonomorphicCalculus.OperationalSemantics.TypeSafety          Spec using (Steps)

open import MonomorphicCalculus.Syntax.Contexts Spec
open import MonomorphicCalculus.Syntax.Terms    Spec
open import MonomorphicCalculus.Syntax.Types    Spec

-- A runtime context is built solely from locks and box-typed cells, so it
-- holds no base-typed variable either (the counterpart of `⇒-not-in-toCtx`,
-- `⦉⦊-not-in-toCtx` and `empty-not-in-toCtx` in `MonomorphicCalculus.OperationalSemantics.State`).

Base-not-in-toCtx : ∀ {Γ ρ b} {𝕊 : State Γ} → Base b ∈[ ρ ] toCtx 𝕊 → ⊥
Base-not-in-toCtx {𝕊 = 𝕊 ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = Base-not-in-toCtx x
Base-not-in-toCtx {𝕊 = 𝕊 ∷ₛ V}   (Tl-∷ x)  = Base-not-in-toCtx x

-- Hence a base-typed value over a state context is a constant underneath its
-- subsumption spine, which `base-val` strips.

base-val : ∀ {b} {𝕊 : State []}
         → toCtx 𝕊 ⊢ᵛ⦂ Base b
         → toCtx 𝕊 ⊢ᵛ⦂ Base b
base-val (var x f)             = ⊥-elim (Base-not-in-toCtx x)
base-val (const B c)           = const B c
base-val (subV V (Baseₛ refl)) = base-val V

base-canonical : ∀ {b} {𝕊 : State []}
               → (V : toCtx 𝕊 ⊢ᵛ⦂ Base b)
               → Σ[ c ∈ BaseConstants b ] base-val V ≡ const b c
base-canonical (var x f)             = ⊥-elim (Base-not-in-toCtx x)
base-canonical (const B c)           = c , refl
base-canonical (subV V (Baseₛ refl)) = base-canonical V

-- The same at `bool`, where the spine is again forced to be identity
-- coercions, and a comparison stands for the constant it decides to.

bool-val : ∀ {𝕊 : State []} → toCtx 𝕊 ⊢ᵛ⦂ bool → toCtx 𝕊 ⊢ᵛ⦂ bool
bool-val (var x f)      = ⊥-elim (bool-not-in-toCtx x)
bool-val true           = true
bool-val false          = false
bool-val {𝕊} (cmp ⋈ V W et) = decide {𝕊 = 𝕊} ⋈ V W et
bool-val (subV V boolₛ) = bool-val V

bool-val-canonical : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ bool)
                   → (bool-val V ≡ true) ⊎ (bool-val V ≡ false)
bool-val-canonical (var x f)      = ⊥-elim (bool-not-in-toCtx x)
bool-val-canonical true           = inj₁ refl
bool-val-canonical false          = inj₂ refl
bool-val-canonical {𝕊} (cmp ⋈ V W et) = decided {𝕊 = 𝕊} ⋈ V W et
bool-val-canonical (subV V boolₛ) = bool-val-canonical V

-- The constant `base-canonical` reads off is the one the value strips to.

base-canonical-const : ∀ {b} {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ Base b)
                     → {c : BaseConstants b}
                     → base-val V ≡ const b c
                     → proj₁ (base-canonical V) ≡ c
base-canonical-const V eq = from (base-canonical V)
  where
    from : (p : Σ[ c' ∈ BaseConstants _ ] base-val V ≡ const _ c') → proj₁ p ≡ _
    from (c' , eq') with trans (sym eq') eq
    ... | refl = refl

-- The boolean a `bool`-typed value strips to.

bool-canonical-value : ∀ {𝕊 : State []} → toCtx 𝕊 ⊢ᵛ⦂ bool → Bool.Bool
bool-canonical-value V = of (bool-val-canonical V)
  where
    of : (bool-val V ≡ true) ⊎ (bool-val V ≡ false) → Bool.Bool
    of (inj₁ _) = Bool.true
    of (inj₂ _) = Bool.false

bool-canonical-true : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ bool)
                    → bool-val V ≡ true → bool-canonical-value V ≡ Bool.true
bool-canonical-true V eq with bool-val-canonical V
... | inj₁ _  = refl
... | inj₂ eq' with trans (sym eq) eq'
...   | ()

bool-canonical-false : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢ᵛ⦂ bool)
                     → bool-val V ≡ false → bool-canonical-value V ≡ Bool.false
bool-canonical-false V eq with bool-val-canonical V
... | inj₂ _  = refl
... | inj₁ eq' with trans (sym eq) eq'
...   | ()

-- The ticks a step takes: only `DELAY` advances time, by its own delay. The
-- grade `steps-grade` is not an observable: it absorbs `𝟏ₑ` factors freely
-- and `_≾ₑ_` is a preorder.

step-ticks : ∀ {ε ε'} {𝕊 𝕊' : State []} {A B : VType}
           → {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → {M' : toCtx 𝕊' ⊢ᶜ⦂ B ! ε'}
           → ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊' ∣ M' ⟩
           → 𝔻
step-ticks APP                 = 0ᴰ
step-ticks MATCH               = 0ᴰ
step-ticks CMP                 = 0ᴰ
step-ticks IF-TRUE             = 0ᴰ
step-ticks IF-FALSE            = 0ᴰ
step-ticks MATCH+              = 0ᴰ
step-ticks MATCHℕ-ZERO         = 0ᴰ
step-ticks MATCHℕ-SUCC         = 0ᴰ
step-ticks RECℕ-ZERO           = 0ᴰ
step-ticks RECℕ-SUCC           = 0ᴰ
step-ticks (SEQ-STEP r _)      = step-ticks r
step-ticks SEQ-RET             = 0ᴰ
step-ticks SEQ-OP              = 0ᴰ
step-ticks (DELAY {τ = τ})     = τ
step-ticks HANDLE-RET          = 0ᴰ
step-ticks (HANDLE-STEP r _)   = step-ticks r
step-ticks HANDLE-OP           = 0ᴰ
step-ticks BOX                 = 0ᴰ
step-ticks UNBOX               = 0ᴰ
step-ticks SUB-APP             = 0ᴰ
step-ticks SUB-HANDLE          = 0ᴰ
step-ticks SUB-HANDLE-TRANS    = 0ᴰ
step-ticks SUB-IF              = 0ᴰ
step-ticks SUB-MATCHℕ          = 0ᴰ
step-ticks SUB-RECℕ            = 0ᴰ
step-ticks MATCHL              = 0ᴰ
step-ticks RECL                = 0ᴰ
step-ticks SUB                 = 0ᴰ

ticks : ∀ {A B ε ε'} {cf : Config (A ! ε)} {cf' : Config (B ! ε')}
      → cf ⟶* cf'
      → 𝔻
ticks done     = 0ᴰ
ticks (r ▸ rs) = step-ticks r +ᴰ ticks rs

-- Halting: a run to a finished computation

Halts : ∀ {A ε} → (𝕊 : State []) → toCtx 𝕊 ⊢ᶜ⦂ A ! ε → Set
Halts 𝕊 M =
  Σ[ B ∈ VType ] Σ[ ε' ∈ E ] Σ[ 𝕊' ∈ State [] ] Σ[ M' ∈ toCtx 𝕊' ⊢ᶜ⦂ B ! ε' ]
    ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊' ∣ M' ⟩ × Final M'

-- How a halted computation finished: it returned, or it called an operation.

data Outcome : Set where
  returned  : Outcome
  performed : Op → Outcome

outcome : ∀ {A ε} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → Halts 𝕊 M → Outcome
outcome (_ , _ , _ , _ , _ , is-return _)       = returned
outcome (_ , _ , _ , _ , _ , is-perform op _ _) = performed op

-- The observable time of a halted computation: its run's tick total.

halt-ticks : ∀ {A ε} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε} → Halts 𝕊 M → 𝔻
halt-ticks (_ , _ , _ , _ , rs , _) = ticks rs

-- A closed computation: one typed in the empty context, which is the context
-- `toCtx ∅` of the empty state.

Closed : VType → E → Set
Closed A ε = [] ⊢ᶜ⦂ A ! ε

-- The two congruences, as maps on steps. The reducts are left to unification:
-- they are whatever the rule builds out of the sub-step.

seq-step : ∀ {A B ε₁ ε₂} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε₁}
         → (N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂)
         → Steps 𝕊 M
         ---------------------
         → Steps 𝕊 (M ⨟ N)
seq-step N (_ , _ , _ , _ , r) = _ , _ , _ , _ , SEQ-STEP r (step-grade-≾ r)

handle-step : ∀ {A B ε₁ ε₂} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε₁}
            → (N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢ᶜ⦂ B ! ε₂)
            → (H : (op : Op) → (ε₃ : E) →
                     toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                             ∷ [ ∣ op-grade op ∣ᵉ ]
                                 (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
                           ⊢ᶜ⦂ B ! (op-grade op ·ₑ ε₃))
            → Steps 𝕊 M
            ------------------------------------------
            → Steps 𝕊 (handle M `with handler N H)
handle-step N H (_ , _ , _ , _ , r) =
  _ , _ , _ , _ , HANDLE-STEP r (step-grade-≾ r)

-- A step out of a configuration is unique, target and derivation alike. Stated
-- as an equation in `Steps`, which keeps it homogeneous, so consumers can match
-- on `refl`.

⟶-det : ∀ {A A₁ A₂ ε ε₁ ε₂} {𝕊 𝕊₁ 𝕊₂ : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
      → {M₁ : toCtx 𝕊₁ ⊢ᶜ⦂ A₁ ! ε₁} → {M₂ : toCtx 𝕊₂ ⊢ᶜ⦂ A₂ ! ε₂}
      → (r₁ : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊₁ ∣ M₁ ⟩) → (r₂ : ⟨ 𝕊 ∣ M ⟩ ⟶ ⟨ 𝕊₂ ∣ M₂ ⟩)
      ---------------------------------------------------------------------------
      → _≡_ {A = Steps 𝕊 M} (A₁ , ε₁ , 𝕊₁ , M₁ , r₁) (A₂ , ε₂ , 𝕊₂ , M₂ , r₂)

-- the rules that fire on a determined term shape
⟶-det APP         APP         = refl
⟶-det MATCH       MATCH       = refl
⟶-det CMP         CMP         = refl
⟶-det IF-TRUE     IF-TRUE     = refl
⟶-det IF-FALSE    IF-FALSE    = refl
⟶-det MATCH+      MATCH+      = refl
⟶-det MATCHℕ-ZERO MATCHℕ-ZERO = refl
⟶-det MATCHℕ-SUCC MATCHℕ-SUCC = refl
⟶-det RECℕ-ZERO   RECℕ-ZERO   = refl
⟶-det RECℕ-SUCC   RECℕ-SUCC   = refl
⟶-det SEQ-RET     SEQ-RET     = refl
⟶-det SEQ-OP      SEQ-OP      = refl
⟶-det DELAY       DELAY       = refl
⟶-det HANDLE-RET  HANDLE-RET  = refl
⟶-det HANDLE-OP   HANDLE-OP   = refl
⟶-det BOX         BOX         = refl
⟶-det UNBOX       UNBOX       = refl
⟶-det SUB-APP     SUB-APP     = refl
⟶-det SUB-HANDLE  SUB-HANDLE  = refl
⟶-det SUB-HANDLE-TRANS SUB-HANDLE-TRANS = refl
⟶-det SUB-IF      SUB-IF      = refl
⟶-det SUB-MATCHℕ  SUB-MATCHℕ  = refl
⟶-det SUB-RECℕ    SUB-RECℕ    = refl
⟶-det MATCHL      MATCHL      = refl
⟶-det RECL        RECL        = refl
⟶-det SUB         SUB         = refl

-- the congruences: normalise the grade premises (they are irrelevant), then
-- rebuild both reducts from the sub-derivations' equality
⟶-det (SEQ-STEP {N = N} r p) (SEQ-STEP r' p')
  rewrite ≾ᵣ-irrelevant p (step-grade-≾ r) | ≾ᵣ-irrelevant p' (step-grade-≾ r') =
  cong (seq-step N) (⟶-det r r')
⟶-det (HANDLE-STEP {H = H} {N = N} r p) (HANDLE-STEP r' p')
  rewrite ≾ᵣ-irrelevant p (step-grade-≾ r) | ≾ᵣ-irrelevant p' (step-grade-≾ r') =
  cong (handle-step N H) (⟶-det r r')
-- a congruence against a finished scrutinee cannot happen
⟶-det (SEQ-STEP r _)    SEQ-RET           = ⊥-elim (final-no-step (is-return _) r)
⟶-det SEQ-RET           (SEQ-STEP r _)    = ⊥-elim (final-no-step (is-return _) r)
⟶-det (SEQ-STEP r _)    SEQ-OP            = ⊥-elim (final-no-step (is-perform _ _ _) r)
⟶-det SEQ-OP            (SEQ-STEP r _)    = ⊥-elim (final-no-step (is-perform _ _ _) r)
⟶-det (HANDLE-STEP r _) HANDLE-RET        = ⊥-elim (final-no-step (is-return _) r)
⟶-det HANDLE-RET        (HANDLE-STEP r _) = ⊥-elim (final-no-step (is-return _) r)
⟶-det (HANDLE-STEP r _) HANDLE-OP         = ⊥-elim (final-no-step (is-perform _ _ _) r)
⟶-det HANDLE-OP         (HANDLE-STEP r _) = ⊥-elim (final-no-step (is-perform _ _ _) r)

-- A computation is finished in one way only.

final-unique : ∀ {Γ C} {M : Γ ⊢ᶜ⦂ C} → (f f' : Final M) → f ≡ f'
final-unique (is-return _)      (is-return _)      = refl
final-unique (is-perform _ _ _) (is-perform _ _ _) = refl

-- A configuration halts in one way only: the run and the finished computation
-- it reaches are unique. Hence so are the outcome and the tick total.

private

  runs-det : ∀ {A B₁ B₂ ε ε₁ ε₂} {𝕊 𝕊₁ 𝕊₂ : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
           → {M₁ : toCtx 𝕊₁ ⊢ᶜ⦂ B₁ ! ε₁} → {M₂ : toCtx 𝕊₂ ⊢ᶜ⦂ B₂ ! ε₂}
           → (rs₁ : ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₁ ∣ M₁ ⟩) → (f₁ : Final M₁)
           → (rs₂ : ⟨ 𝕊 ∣ M ⟩ ⟶* ⟨ 𝕊₂ ∣ M₂ ⟩) → (f₂ : Final M₂)
           → _≡_ {A = Halts 𝕊 M} (B₁ , ε₁ , 𝕊₁ , M₁ , rs₁ , f₁)
                                 (B₂ , ε₂ , 𝕊₂ , M₂ , rs₂ , f₂)
  runs-det done f₁ done f₂ with final-unique f₁ f₂
  ... | refl = refl
  runs-det done    f₁ (r ▸ _) _  = ⊥-elim (final-no-step f₁ r)
  runs-det (r ▸ _) _  done    f₂ = ⊥-elim (final-no-step f₂ r)
  runs-det (_▸_ {cf₂ = ⟨ _ ∣ _ ⟩} r₁ rs₁) f₁ (_▸_ {cf₂ = ⟨ _ ∣ _ ⟩} r₂ rs₂) f₂
    with ⟶-det r₁ r₂
  ... | refl with runs-det rs₁ f₁ rs₂ f₂
  ...   | refl = refl

halts-det : ∀ {A ε} {𝕊 : State []} {M : toCtx 𝕊 ⊢ᶜ⦂ A ! ε}
          → (h h' : Halts 𝕊 M)
          ----------------------
          → h ≡ h'
halts-det (_ , _ , _ , _ , rs , f) (_ , _ , _ , _ , rs' , f') = runs-det rs f rs' f'
