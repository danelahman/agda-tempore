------------------------------------------------------------------------
-- Weak-head evaluation: the two shapes a configuration halts in.     --
--                                                                    --
-- `progress` halts a configuration at a `return` or at an unhandled  --
-- `perform` (`Progress`'s `is-return`/`is-perform`), and both are    --
-- final. Packaged as evaluation relations on configurations,         --
-- together with the run's observable time, its tick total.           --
--                                                                    --
-- Syntactic: no model parameters.                                    --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_)

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
         → toCtx 𝕊 ⊢V⦂ Base b
         → toCtx 𝕊 ⊢V⦂ Base b
base-val (var f x)             = ⊥-elim (Base-not-in-toCtx x)
base-val (const B c)           = const B c
base-val (subV V (Baseₛ refl)) = base-val V

base-canonical : ∀ {b} {𝕊 : State []}
               → (V : toCtx 𝕊 ⊢V⦂ Base b)
               → Σ[ c ∈ BaseConstants b ] base-val V ≡ const b c
base-canonical (var f x)             = ⊥-elim (Base-not-in-toCtx x)
base-canonical (const B c)           = c , refl
base-canonical (subV V (Baseₛ refl)) = base-canonical V

-- The same at `bool`, where the spine is again forced to be identity
-- coercions.

bool-val : ∀ {𝕊 : State []} → toCtx 𝕊 ⊢V⦂ bool → toCtx 𝕊 ⊢V⦂ bool
bool-val (var f x)      = ⊥-elim (bool-not-in-toCtx x)
bool-val true           = true
bool-val false          = false
bool-val (subV V boolₛ) = bool-val V

bool-val-canonical : ∀ {𝕊 : State []} → (V : toCtx 𝕊 ⊢V⦂ bool)
                   → (bool-val V ≡ true) ⊎ (bool-val V ≡ false)
bool-val-canonical (var f x)      = ⊥-elim (bool-not-in-toCtx x)
bool-val-canonical true           = inj₁ refl
bool-val-canonical false          = inj₂ refl
bool-val-canonical (subV V boolₛ) = bool-val-canonical V

-- The ticks a step takes: only `DELAY` advances time, by its own delay. The
-- grade `steps-grade` is not an observable: it absorbs `𝟏ₑ` factors freely
-- and `_≾ₑ_` is a preorder.

step-ticks : ∀ {ε ε'} {𝕊 𝕊' : State []} {A B : VType}
           → {M : toCtx 𝕊 ⊢C⦂ A ! ε} → {M' : toCtx 𝕊' ⊢C⦂ B ! ε'}
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

-- Evaluation to a returned value.

record Ret-whnf {A : VType} {ε : E} (cf : Config (A ! ε)) : Set where
  constructor ret-whnf
  field
    state : State []
    vtype : VType
    value : toCtx state ⊢V⦂ vtype
    run   : cf ⟶* ⟨ state ∣ return value ⟩

-- Evaluation to an unhandled operation, with its parameter and continuation.

record Op-whnf {A : VType} {ε : E} (cf : Config (A ! ε)) : Set where
  constructor op-whnf
  field
    state : State []
    oper  : Op
    resid : E
    vtype : VType
    prm   : toCtx state ⊢V⦂ ⌜ param oper ⌝ᵍ
    cont  : toCtx state ⟨ ∣ op-grade oper ∣ᵉ ⟩ ∷ ⌜ arity oper ⌝ᵍ
              ⊢C⦂ vtype ! resid
    run   : cf ⟶* ⟨ state ∣ perform oper prm cont ⟩

data Halts {A : VType} {ε : E} (cf : Config (A ! ε)) : Set where
  halts-ret : Ret-whnf cf → Halts cf
  halts-op  : Op-whnf  cf → Halts cf

-- The observable time of an evaluation.

ret-ticks : ∀ {A ε} {cf : Config (A ! ε)} → Ret-whnf cf → 𝔻
ret-ticks w = ticks (Ret-whnf.run w)

op-ticks : ∀ {A ε} {cf : Config (A ! ε)} → Op-whnf cf → 𝔻
op-ticks w = ticks (Op-whnf.run w)

-- A closed computation: one typed in the empty context, which is the context
-- `toCtx ∅` of the empty state.

Closed : VType → E → Set
Closed A ε = [] ⊢C⦂ A ! ε

-- Neither whnf steps.

finality-ret : ∀ {A} {D : CType} {𝕊 : State []}
             → {V : toCtx 𝕊 ⊢V⦂ A} → {cf : Config D}
             → ⟨ 𝕊 ∣ return V ⟩ ⟶ cf
             ------------------------
             → ⊥
finality-ret ()

finality-perform : ∀ {A ε op} {D : CType} {𝕊 : State []}
                 → {W : toCtx 𝕊 ⊢V⦂ ⌜ param op ⌝ᵍ}
                 → {M : toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                          ⊢C⦂ A ! ε}
                 → {cf : Config D}
                 → ⟨ 𝕊 ∣ perform op W M ⟩ ⟶ cf
                 -----------------------------
                 → ⊥
finality-perform ()

-- A step out of a configuration is unique, target and derivation alike. Packing
-- grade, target and derivation into one Σ keeps the statement homogeneous, so
-- consumers can match on `refl`.

Step-from : ∀ {A ε} → (cf : Config (A ! ε)) → Set
Step-from cf =
  Σ[ A' ∈ VType ] Σ[ ε' ∈ E ] Σ[ cf' ∈ Config (A' ! ε') ] (cf ⟶ cf')

-- The two congruences, as maps on packed steps. The reducts are left to
-- unification: they are whatever the rule builds out of the sub-step.

seq-step : ∀ {A B ε₁ ε₂} {𝕊 : State []} {M : toCtx 𝕊 ⊢C⦂ A ! ε₁}
         → (N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂)
         → Step-from (⟨ 𝕊 ∣ M ⟩)
         ---------------------------------
         → Step-from (⟨ 𝕊 ∣ M ⨟ N ⟩)
seq-step N (A₀ , ε₃ , ⟨ 𝕊' ∣ M' ⟩ , r) = _ , _ , _ , SEQ-STEP r (step-grade-≾ r)

handle-step : ∀ {A B ε₁ ε₂} {𝕊 : State []} {M : toCtx 𝕊 ⊢C⦂ A ! ε₁}
            → (N : toCtx 𝕊 ⟨ ∣ ε₁ ∣ᵉ ⟩ ∷ A ⊢C⦂ B ! ε₂)
            → (H : (op : Op) → (ε₃ : E) →
                     toCtx 𝕊 ⟨ ⊤ᵣ ⟩ ∷ ⌜ param op ⌝ᵍ
                             ∷ [ ∣ op-grade op ∣ᵉ ]
                                 (⌜ arity op ⌝ᵍ ⇒ B ! ε₃)
                           ⊢C⦂ B ! (op-grade op ·ₑ ε₃))
            → Step-from (⟨ 𝕊 ∣ M ⟩)
            ------------------------------------------------------
            → Step-from (⟨ 𝕊 ∣ handle M `with handler N H ⟩)
handle-step N H (A₀ , ε₃ , ⟨ 𝕊' ∣ M' ⟩ , r) =
  _ , _ , _ , HANDLE-STEP r (step-grade-≾ r)

⟶-det : ∀ {A A₁ A₂ ε ε₁ ε₂} {cf : Config (A ! ε)}
      → {cf₁ : Config (A₁ ! ε₁)} → {cf₂ : Config (A₂ ! ε₂)}
      → (r₁ : cf ⟶ cf₁) → (r₂ : cf ⟶ cf₂)
      -----------------------------------------------------------
      → _≡_ {A = Step-from cf} (A₁ , ε₁ , cf₁ , r₁) (A₂ , ε₂ , cf₂ , r₂)

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
-- a congruence against a whnf scrutinee cannot happen
⟶-det (SEQ-STEP r _)    SEQ-RET          = ⊥-elim (finality-ret r)
⟶-det SEQ-RET           (SEQ-STEP r _)   = ⊥-elim (finality-ret r)
⟶-det (SEQ-STEP r _)    SEQ-OP           = ⊥-elim (finality-perform r)
⟶-det SEQ-OP            (SEQ-STEP r _)   = ⊥-elim (finality-perform r)
⟶-det (HANDLE-STEP r _) HANDLE-RET       = ⊥-elim (finality-ret r)
⟶-det HANDLE-RET        (HANDLE-STEP r _) = ⊥-elim (finality-ret r)
⟶-det (HANDLE-STEP r _) HANDLE-OP        = ⊥-elim (finality-perform r)
⟶-det HANDLE-OP         (HANDLE-STEP r _) = ⊥-elim (finality-perform r)

Op-run : ∀ {A ε} → (cf : Config (A ! ε)) → Set
Op-run cf =
  Σ[ 𝕊 ∈ State [] ] Σ[ op ∈ Op ] Σ[ A' ∈ VType ] Σ[ ε' ∈ E ]
  Σ[ W ∈ toCtx 𝕊 ⊢V⦂ ⌜ param op ⌝ᵍ ]
  Σ[ M ∈ (toCtx 𝕊 ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ ⊢C⦂ A' ! ε') ]
    (cf ⟶* ⟨ 𝕊 ∣ perform op W M ⟩)

op-run-det : ∀ {A ε} {cf : Config (A ! ε)}
           → {𝕊₁ 𝕊₂ : State []} → {op₁ op₂ : Op} → {A₁ A₂ : VType} → {ε₁' ε₂' : E}
           → {W₁ : toCtx 𝕊₁ ⊢V⦂ ⌜ param op₁ ⌝ᵍ}
           → {W₂ : toCtx 𝕊₂ ⊢V⦂ ⌜ param op₂ ⌝ᵍ}
           → {M₁ : toCtx 𝕊₁ ⟨ ∣ op-grade op₁ ∣ᵉ ⟩ ∷ ⌜ arity op₁ ⌝ᵍ
                     ⊢C⦂ A₁ ! ε₁'}
           → {M₂ : toCtx 𝕊₂ ⟨ ∣ op-grade op₂ ∣ᵉ ⟩ ∷ ⌜ arity op₂ ⌝ᵍ
                     ⊢C⦂ A₂ ! ε₂'}
           → (rs₁ : cf ⟶* ⟨ 𝕊₁ ∣ perform op₁ W₁ M₁ ⟩)
           → (rs₂ : cf ⟶* ⟨ 𝕊₂ ∣ perform op₂ W₂ M₂ ⟩)
           ---------------------------------------------------------------
           → _≡_ {A = Op-run cf} (𝕊₁ , op₁ , A₁ , ε₁' , W₁ , M₁ , rs₁)
                                 (𝕊₂ , op₂ , A₂ , ε₂' , W₂ , M₂ , rs₂)

op-run-det done       done       = refl
op-run-det done       (r ▸ _)    = ⊥-elim (finality-perform r)
op-run-det (r ▸ _)    done       = ⊥-elim (finality-perform r)
op-run-det (r₁ ▸ rs₁) (r₂ ▸ rs₂) with ⟶-det r₁ r₂
... | refl =
  cong (λ z → proj₁ z , proj₁ (proj₂ z) , proj₁ (proj₂ (proj₂ z))
             , proj₁ (proj₂ (proj₂ (proj₂ z)))
             , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ z))))
             , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z)))))
             , r₁ ▸ proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z))))))
       (op-run-det rs₁ rs₂)

-- The two shapes exclude each other.

⇓-exclusive : ∀ {A ε} {cf : Config (A ! ε)} → Ret-whnf cf → Op-whnf cf → ⊥
⇓-exclusive w w' = no-both (Ret-whnf.run w) (Op-whnf.run w')
  where
    no-both : ∀ {A A₁ A₂ ε ε'} {cf : Config (A ! ε)}
            → {𝕊₁ 𝕊₂ : State []} {op : Op}
            → {V : toCtx 𝕊₁ ⊢V⦂ A₁}
            → {W : toCtx 𝕊₂ ⊢V⦂ ⌜ param op ⌝ᵍ}
            → {M : toCtx 𝕊₂ ⟨ ∣ op-grade op ∣ᵉ ⟩ ∷ ⌜ arity op ⌝ᵍ
                     ⊢C⦂ A₂ ! ε'}
            → cf ⟶* ⟨ 𝕊₁ ∣ return V ⟩
            → cf ⟶* ⟨ 𝕊₂ ∣ perform op W M ⟩
            → ⊥
    no-both done       (r ▸ _)    = finality-ret r
    no-both (r ▸ _)    done       = finality-perform r
    no-both (r₁ ▸ rs₁) (r₂ ▸ rs₂) with ⟶-det r₁ r₂
    ... | refl = no-both rs₁ rs₂

op-whnf-unique : ∀ {A ε} {cf : Config (A ! ε)} → (w w' : Op-whnf cf)
               → Σ[ e ∈ Op-whnf.oper w ≡ Op-whnf.oper w' ]
                   (op-ticks w ≡ op-ticks w')
op-whnf-unique w w' =
    cong (λ z → proj₁ (proj₂ z)) eq
  , cong (λ z → ticks (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z))))))) eq
  where
    eq = op-run-det (Op-whnf.run w) (Op-whnf.run w')
