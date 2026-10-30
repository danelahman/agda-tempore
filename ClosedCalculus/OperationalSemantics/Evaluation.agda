------------------------------------------------------------------------
-- Weak-head evaluation: the two shapes a configuration halts in.     --
--                                                                    --
-- `progress` halts a configuration at a `return` or at an unhandled  --
-- `perform` (`Progress`'s `is-value`/`is-op`), and both are          --
-- final. Packaged here as evaluation relations on configurations,    --
-- together with the run's observable time (its *tick total*).        --
--                                                                    --
-- Purely syntactic: no model parameters.                             --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Relation.Nullary using (¬_)

open import Grades.Base
open import Language.Spec
open import Language.Operations

open import Util.Equality

module ClosedCalculus.OperationalSemantics.Evaluation (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import ClosedCalculus.OperationalSemantics.Reduction           Spec
open import ClosedCalculus.OperationalSemantics.State               Spec

open import ClosedCalculus.Syntax.Contexts Spec
open import ClosedCalculus.Syntax.Terms    Spec
open import ClosedCalculus.Syntax.Types    Spec

-- A runtime context is built solely from locks and box-typed cells, so it
-- holds no base-typed variable either (the counterpart of `⇒-not-in-toCtx`,
-- `⦉⦊-not-in-toCtx` and `Empty-not-in-toCtx` in `ClosedCalculus.OperationalSemantics.State`).

Base-not-in-toCtx : ∀ {Γ ρ b} {St : 𝕊 Γ} → Base b ∈[ ρ ] toCtx St → ⊥
Base-not-in-toCtx {St = St ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = Base-not-in-toCtx x
Base-not-in-toCtx {St = St ∷ₛ V}   (Tl-∷ x)  = Base-not-in-toCtx x

-- Hence a base-typed value over a state context is a constant underneath its
-- subsumption spine, which `base-val` strips.

base-val : ∀ {b} {St : 𝕊 []}
         → toCtx St ⊢V⦂ Base b
         → toCtx St ⊢V⦂ Base b
base-val (var f x)             = ⊥-elim (Base-not-in-toCtx x)
base-val (const c)             = const c
base-val (subV V (Baseₛ refl)) = base-val V

base-canonical : ∀ {b} {St : 𝕊 []}
               → (V : toCtx St ⊢V⦂ Base b)
               → Σ[ c ∈ BaseConstants b ] base-val V ≡ const c
base-canonical (var f x)             = ⊥-elim (Base-not-in-toCtx x)
base-canonical (const c)             = c , refl
base-canonical (subV V (Baseₛ refl)) = base-canonical V

-- The same at `Bool`, where the spine is again forced to be identity
-- coercions.

bool-val : ∀ {St : 𝕊 []} → toCtx St ⊢V⦂ Bool → toCtx St ⊢V⦂ Bool
bool-val (var f x)      = ⊥-elim (Bool-not-in-toCtx x)
bool-val true           = true
bool-val false          = false
bool-val (subV V Boolₛ) = bool-val V

bool-val-canonical : ∀ {St : 𝕊 []} → (V : toCtx St ⊢V⦂ Bool)
                   → (bool-val V ≡ true) ⊎ (bool-val V ≡ false)
bool-val-canonical (var f x)      = ⊥-elim (Bool-not-in-toCtx x)
bool-val-canonical true           = inj₁ refl
bool-val-canonical false          = inj₂ refl
bool-val-canonical (subV V Boolₛ) = bool-val-canonical V

-- The ticks a step takes: only `DELAY` advances time, by its own delay. The
-- grade `steps-grade` is not an observable — it absorbs `uₑ` factors freely
-- and `_≾ₑ_` is a preorder.

step-ticks : ∀ {ε ε'} {St St' : 𝕊 []} {A B : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
           → ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩
           → 𝔻
step-ticks APP                 = 0ᴰ
step-ticks MATCH               = 0ᴰ
step-ticks CMP                 = 0ᴰ
step-ticks IF-TRUE             = 0ᴰ
step-ticks IF-FALSE            = 0ᴰ
step-ticks CASE+               = 0ᴰ
step-ticks CASEℕ-ZERO          = 0ᴰ
step-ticks CASEℕ-SUCC          = 0ᴰ
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
step-ticks SUB-IF              = 0ᴰ
step-ticks SUB-CASEℕ           = 0ᴰ
step-ticks SUB-RECℕ            = 0ᴰ
step-ticks CASEL               = 0ᴰ
step-ticks RECL                = 0ᴰ
step-ticks SUB                 = 0ᴰ

ticks : ∀ {A B ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (B ‼ ε')}
      → cf ↝* cf'
      → 𝔻
ticks ε*       = 0ᴰ
ticks (r ◅ rs) = step-ticks r +ᴰ ticks rs

-- Evaluation to a returned value.

record Ret-whnf {A : VType} {ε : E} (cf : Config (A ‼ ε)) : Set where
  constructor ret-whnf
  field
    state : 𝕊 []
    vtype : VType
    value : toCtx state ⊢V⦂ vtype
    run   : cf ↝* ⟨ state , return value ⟩

-- Evaluation to an unhandled operation, with its parameter and continuation.

record Op-whnf {A : VType} {ε : E} (cf : Config (A ‼ ε)) : Set where
  constructor op-whnf
  field
    state : 𝕊 []
    oper  : Op
    resid : E
    vtype : VType
    prm   : toCtx state ⊢V⦂ type-of-gtype (param oper)
    cont  : toCtx state ⟨ mapᵉ (op-grade oper) ⟩ ∷ type-of-gtype (arity oper)
              ⊢C⦂ vtype ‼ resid
    run   : cf ↝* ⟨ state , perform oper prm cont ⟩

data Halts {A : VType} {ε : E} (cf : Config (A ‼ ε)) : Set where
  halts-ret : Ret-whnf cf → Halts cf
  halts-op  : Op-whnf  cf → Halts cf

-- The observable time of an evaluation.

ret-ticks : ∀ {A ε} {cf : Config (A ‼ ε)} → Ret-whnf cf → 𝔻
ret-ticks w = ticks (Ret-whnf.run w)

op-ticks : ∀ {A ε} {cf : Config (A ‼ ε)} → Op-whnf cf → 𝔻
op-ticks w = ticks (Op-whnf.run w)

-- `toCtx ∅ ≡ []`, so this is `ClosedCalculus.OperationalSemantics.Soundness.Preservation`'s
-- `Program` (definitionally), stated without model parameters.

Prog : VType → E → Set
Prog A ε = toCtx {[]} ∅ ⊢C⦂ A ‼ ε

-- Neither whnf steps.

finality-ret : ∀ {A} {D : CType} {St : 𝕊 []}
             → {V : toCtx St ⊢V⦂ A} → {cf : Config D}
             → ⟨ St , return V ⟩ ↝ cf
             ------------------------
             → ⊥
finality-ret ()

finality-perform : ∀ {A ε op} {D : CType} {St : 𝕊 []}
                 → {W : toCtx St ⊢V⦂ type-of-gtype (param op)}
                 → {M : toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                          ⊢C⦂ A ‼ ε}
                 → {cf : Config D}
                 → ⟨ St , perform op W M ⟩ ↝ cf
                 -----------------------------
                 → ⊥
finality-perform ()

-- A step out of a configuration is unique — target and derivation. Packing
-- grade, target and derivation into one Σ keeps the statement homogeneous, so
-- consumers can match on `refl`.

Step-from : ∀ {A ε} → (cf : Config (A ‼ ε)) → Set
Step-from cf =
  Σ[ A' ∈ VType ] Σ[ ε' ∈ E ] Σ[ cf' ∈ Config (A' ‼ ε') ] (cf ↝ cf')

-- The two congruences, as maps on packed steps. The reducts are left to
-- unification: they are whatever the rule builds out of the sub-step.

seq-step : ∀ {A B ε₁ ε₂} {St : 𝕊 []} {M : toCtx St ⊢C⦂ A ‼ ε₁}
         → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
         → Step-from (⟨ St , M ⟩)
         ---------------------------------
         → Step-from (⟨ St , M ⨟ N ⟩)
seq-step N (A₀ , ε₃ , ⟨ St' , M' ⟩ , r) = _ , _ , _ , SEQ-STEP r (step-grade-≾ r)

handle-step : ∀ {A B ε₁ ε₂} {St : 𝕊 []} {M : toCtx St ⊢C⦂ A ‼ ε₁}
            → (H : (op : Op) → (ε₃ : E) →
                     toCtx St ⟨ ⊤ᵣ ⟩ ∷ type-of-gtype (param op)
                             ∷ [ mapᵉ (op-grade op) ]
                                 (type-of-gtype (arity op) ⇒ B ‼ ε₃)
                           ⊢C⦂ B ‼ (op-grade op ·ₑ ε₃))
            → (N : toCtx St ⟨ mapᵉ ε₁ ⟩ ∷ A ⊢C⦂ B ‼ ε₂)
            → Step-from (⟨ St , M ⟩)
            ------------------------------------------------
            → Step-from (⟨ St , handle M `with H `in N ⟩)
handle-step H N (A₀ , ε₃ , ⟨ St' , M' ⟩ , r) =
  _ , _ , _ , HANDLE-STEP r (step-grade-≾ r)

↝-det : ∀ {A A₁ A₂ ε ε₁ ε₂} {cf : Config (A ‼ ε)}
      → {cf₁ : Config (A₁ ‼ ε₁)} → {cf₂ : Config (A₂ ‼ ε₂)}
      → (r₁ : cf ↝ cf₁) → (r₂ : cf ↝ cf₂)
      -----------------------------------------------------------
      → _≡_ {A = Step-from cf} (A₁ , ε₁ , cf₁ , r₁) (A₂ , ε₂ , cf₂ , r₂)

-- the rules that fire on a determined term shape
↝-det APP        APP        = refl
↝-det MATCH      MATCH      = refl
↝-det CMP        CMP        = refl
↝-det IF-TRUE    IF-TRUE    = refl
↝-det IF-FALSE   IF-FALSE   = refl
↝-det CASE+      CASE+      = refl
↝-det CASEℕ-ZERO CASEℕ-ZERO = refl
↝-det CASEℕ-SUCC CASEℕ-SUCC = refl
↝-det RECℕ-ZERO  RECℕ-ZERO  = refl
↝-det RECℕ-SUCC  RECℕ-SUCC  = refl
↝-det SEQ-RET    SEQ-RET    = refl
↝-det SEQ-OP     SEQ-OP     = refl
↝-det DELAY      DELAY      = refl
↝-det HANDLE-RET HANDLE-RET = refl
↝-det HANDLE-OP  HANDLE-OP  = refl
↝-det BOX        BOX        = refl
↝-det UNBOX      UNBOX      = refl
↝-det SUB-APP    SUB-APP    = refl
↝-det SUB-IF     SUB-IF     = refl
↝-det SUB-CASEℕ  SUB-CASEℕ  = refl
↝-det SUB-RECℕ   SUB-RECℕ   = refl
↝-det CASEL      CASEL      = refl
↝-det RECL       RECL       = refl
↝-det SUB        SUB        = refl

-- the congruences: normalise the grade premises (they are irrelevant), then
-- rebuild both reducts from the sub-derivations' equality
↝-det (SEQ-STEP {N = N} r p) (SEQ-STEP r' p')
  rewrite ≾ᵣ-irrelevant p (step-grade-≾ r) | ≾ᵣ-irrelevant p' (step-grade-≾ r') =
  cong (seq-step N) (↝-det r r')
↝-det (HANDLE-STEP {H = H} {N = N} r p) (HANDLE-STEP r' p')
  rewrite ≾ᵣ-irrelevant p (step-grade-≾ r) | ≾ᵣ-irrelevant p' (step-grade-≾ r') =
  cong (handle-step H N) (↝-det r r')
-- a congruence against a whnf scrutinee cannot happen
↝-det (SEQ-STEP r _)    SEQ-RET          = ⊥-elim (finality-ret r)
↝-det SEQ-RET           (SEQ-STEP r _)   = ⊥-elim (finality-ret r)
↝-det (SEQ-STEP r _)    SEQ-OP           = ⊥-elim (finality-perform r)
↝-det SEQ-OP            (SEQ-STEP r _)   = ⊥-elim (finality-perform r)
↝-det (HANDLE-STEP r _) HANDLE-RET       = ⊥-elim (finality-ret r)
↝-det HANDLE-RET        (HANDLE-STEP r _) = ⊥-elim (finality-ret r)
↝-det (HANDLE-STEP r _) HANDLE-OP        = ⊥-elim (finality-perform r)
↝-det HANDLE-OP         (HANDLE-STEP r _) = ⊥-elim (finality-perform r)

Op-run : ∀ {A ε} → (cf : Config (A ‼ ε)) → Set
Op-run cf =
  Σ[ St ∈ 𝕊 [] ] Σ[ op ∈ Op ] Σ[ A' ∈ VType ] Σ[ ε' ∈ E ]
  Σ[ W ∈ toCtx St ⊢V⦂ type-of-gtype (param op) ]
  Σ[ M ∈ (toCtx St ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A' ‼ ε') ]
    (cf ↝* ⟨ St , perform op W M ⟩)

op-run-det : ∀ {A ε} {cf : Config (A ‼ ε)}
           → {St₁ St₂ : 𝕊 []} → {op₁ op₂ : Op} → {A₁ A₂ : VType} → {ε₁' ε₂' : E}
           → {W₁ : toCtx St₁ ⊢V⦂ type-of-gtype (param op₁)}
           → {W₂ : toCtx St₂ ⊢V⦂ type-of-gtype (param op₂)}
           → {M₁ : toCtx St₁ ⟨ mapᵉ (op-grade op₁) ⟩ ∷ type-of-gtype (arity op₁)
                     ⊢C⦂ A₁ ‼ ε₁'}
           → {M₂ : toCtx St₂ ⟨ mapᵉ (op-grade op₂) ⟩ ∷ type-of-gtype (arity op₂)
                     ⊢C⦂ A₂ ‼ ε₂'}
           → (rs₁ : cf ↝* ⟨ St₁ , perform op₁ W₁ M₁ ⟩)
           → (rs₂ : cf ↝* ⟨ St₂ , perform op₂ W₂ M₂ ⟩)
           ---------------------------------------------------------------
           → _≡_ {A = Op-run cf} (St₁ , op₁ , A₁ , ε₁' , W₁ , M₁ , rs₁)
                                 (St₂ , op₂ , A₂ , ε₂' , W₂ , M₂ , rs₂)

op-run-det ε*         ε*         = refl
op-run-det ε*         (r ◅ _)    = ⊥-elim (finality-perform r)
op-run-det (r ◅ _)    ε*         = ⊥-elim (finality-perform r)
op-run-det (r₁ ◅ rs₁) (r₂ ◅ rs₂) with ↝-det r₁ r₂
... | refl =
  cong (λ z → proj₁ z , proj₁ (proj₂ z) , proj₁ (proj₂ (proj₂ z))
             , proj₁ (proj₂ (proj₂ (proj₂ z)))
             , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ z))))
             , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z)))))
             , r₁ ◅ proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z))))))
       (op-run-det rs₁ rs₂)

-- The two shapes exclude each other.

⇓-exclusive : ∀ {A ε} {cf : Config (A ‼ ε)} → Ret-whnf cf → Op-whnf cf → ⊥
⇓-exclusive w w' = no-both (Ret-whnf.run w) (Op-whnf.run w')
  where
    no-both : ∀ {A A₁ A₂ ε ε'} {cf : Config (A ‼ ε)}
            → {St₁ St₂ : 𝕊 []} {op : Op}
            → {V : toCtx St₁ ⊢V⦂ A₁}
            → {W : toCtx St₂ ⊢V⦂ type-of-gtype (param op)}
            → {M : toCtx St₂ ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op)
                     ⊢C⦂ A₂ ‼ ε'}
            → cf ↝* ⟨ St₁ , return V ⟩
            → cf ↝* ⟨ St₂ , perform op W M ⟩
            → ⊥
    no-both ε*         (r ◅ _)    = finality-ret r
    no-both (r ◅ _)    ε*         = finality-perform r
    no-both (r₁ ◅ rs₁) (r₂ ◅ rs₂) with ↝-det r₁ r₂
    ... | refl = no-both rs₁ rs₂

op-whnf-unique : ∀ {A ε} {cf : Config (A ‼ ε)} → (w w' : Op-whnf cf)
               → Σ[ e ∈ Op-whnf.oper w ≡ Op-whnf.oper w' ]
                   (op-ticks w ≡ op-ticks w')
op-whnf-unique w w' =
    cong (λ z → proj₁ (proj₂ z)) eq
  , cong (λ z → ticks (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ z))))))) eq
  where
    eq = op-run-det (Op-whnf.run w) (Op-whnf.run w')
