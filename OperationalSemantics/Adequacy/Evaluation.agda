------------------------------------------------------------------------
-- Weak-head evaluation: the two shapes a configuration halts in.      --
--                                                                    --
-- `progress` halts a configuration at a `return` or at an unhandled   --
-- `perform` (`ProgressTheorem`'s `is-value`/`is-op`), and both are     --
-- final. Packaged here as evaluation relations on configurations,      --
-- together with the run's observable time (its *tick total*).          --
--                                                                    --
-- Purely syntactic: no model parameters. See `notes/adequacy-plan.md`. --
------------------------------------------------------------------------

open import Data.Empty
open import Data.Product

open import Relation.Nullary using (¬_)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module OperationalSemantics.Adequacy.Evaluation (Spec : LanguageSpec) where

open LanguageSpec Spec
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem Spec
open import OperationalSemantics.State               Spec

open import Syntax.Contexts Spec
open import Syntax.Language Spec
open import Syntax.Types    Spec

-- CANONICAL FORMS OVER A STATE CONTEXT
--
-- A runtime context is built solely from locks and box-typed cells, so it
-- holds no base-typed variable either (the counterpart of `⇒-not-in-toCtx`,
-- `⦉⦊-not-in-toCtx` and `Empty-not-in-toCtx` in `OperationalSemantics.State`).

Base-not-in-toCtx : ∀ {Γ ρ b} {St : 𝕊 Γ} → Base b ∈[ ρ ] toCtx St → ⊥
Base-not-in-toCtx {St = St ⟨ ρ ⟩ₛ} (Tl-⟨⟩ x) = Base-not-in-toCtx x
Base-not-in-toCtx {St = St ∷ₛ V}   (Tl-∷ x)  = Base-not-in-toCtx x

-- Hence a base-typed value over a state context is a constant.

base-canonical : ∀ {b} {St : 𝕊 []}
               → (V : toCtx St ⊢V⦂ Base b)
               → Σ[ c ∈ BaseConstants b ] V ≡ const c
base-canonical (var f x) = ⊥-elim (Base-not-in-toCtx x)
base-canonical (const c) = c , refl

-- THE OBSERVABLE TIME OF A RUN
--
-- The ticks a step takes: only `DELAY` advances time, and it does so by
-- exactly its own delay. (The grade `steps-grade` is not an observable: it
-- absorbs `uₑ` factors freely and `_≾ₑ_` is only a preorder.)

step-ticks : ∀ {ε ε'} {St St' : 𝕊 []} {A B : VType}
           → {M : toCtx St ⊢C⦂ A ‼ ε} → {M' : toCtx St' ⊢C⦂ B ‼ ε'}
           → ⟨ St , M ⟩ ↝ ⟨ St' , M' ⟩
           → ℕ
step-ticks APP                 = 0
step-ticks MATCH               = 0
step-ticks (SEQ-STEP r _)      = step-ticks r
step-ticks SEQ-RET             = 0
step-ticks SEQ-OP              = 0
step-ticks (DELAY {τ = τ})     = τ
step-ticks HANDLE-RET          = 0
step-ticks (HANDLE-STEP r _)   = step-ticks r
step-ticks HANDLE-OP           = 0
step-ticks BOX                 = 0
step-ticks UNBOX               = 0
step-ticks COERCE              = 0

ticks : ∀ {A ε ε'} {cf : Config (A ‼ ε)} {cf' : Config (A ‼ ε')}
      → cf ↝* cf'
      → ℕ
ticks ε*       = 0
ticks (r ◅ rs) = step-ticks r + ticks rs

-- THE TWO HALTING SHAPES

-- Evaluation to a returned value.

record Ret-whnf {A : VType} {ε : E} (cf : Config (A ‼ ε)) : Set where
  constructor ret-whnf
  field
    state : 𝕊 []
    value : toCtx state ⊢V⦂ A
    run   : cf ↝* ⟨ state , return value ⟩

-- Evaluation to an unhandled operation, with its parameter and continuation.

record Op-whnf {A : VType} {ε : E} (cf : Config (A ‼ ε)) : Set where
  constructor op-whnf
  field
    state : 𝕊 []
    oper  : Op
    resid : E
    prm   : toCtx state ⊢V⦂ type-of-gtype (param oper)
    cont  : toCtx state ⟨ mapᵉ (op-grade oper) ⟩ ∷ type-of-gtype (arity oper)
              ⊢C⦂ A ‼ resid
    run   : cf ↝* ⟨ state , perform oper prm cont ⟩

data Halts {A : VType} {ε : E} (cf : Config (A ‼ ε)) : Set where
  halts-ret : Ret-whnf cf → Halts cf
  halts-op  : Op-whnf  cf → Halts cf

-- The observable time of an evaluation.

ret-ticks : ∀ {A ε} {cf : Config (A ‼ ε)} → Ret-whnf cf → ℕ
ret-ticks w = ticks (Ret-whnf.run w)

op-ticks : ∀ {A ε} {cf : Config (A ‼ ε)} → Op-whnf cf → ℕ
op-ticks w = ticks (Op-whnf.run w)

-- CLOSED PROGRAMS
--
-- `toCtx ∅ ≡ []`, so this is `OperationalSemantics.Soundness.Preservation`'s
-- `Program` (definitionally), stated without model parameters.

Prog : VType → E → Set
Prog A ε = toCtx {[]} ∅ ⊢C⦂ A ‼ ε

------------------------------------------------------------------------
-- LEMMAS TO PROVE
------------------------------------------------------------------------

postulate

  -- Reduction is deterministic. Both the grade and the configuration are
  -- determined; the grade equality mediates the configuration one.

  ↝-deterministic : ∀ {A ε ε₁ ε₂}
                  → {cf : Config (A ‼ ε)}
                  → {cf₁ : Config (A ‼ ε₁)} → {cf₂ : Config (A ‼ ε₂)}
                  → cf ↝ cf₁ → cf ↝ cf₂
                  → Σ[ e ∈ ε₁ ≡ ε₂ ] subst (λ ε' → Config (A ‼ ε')) e cf₁ ≡ cf₂

  -- Hence the two halting shapes exclude each other: no configuration both
  -- returns a value and gets stuck on an operation. Needs `↝-deterministic`
  -- together with `finality-value`/`finality-op`.

  ⇓-exclusive : ∀ {A ε} {cf : Config (A ‼ ε)} → Ret-whnf cf → Op-whnf cf → ⊥

  -- And each shape is unique when it is reached, including its time.

  ret-whnf-unique : ∀ {A ε} {cf : Config (A ‼ ε)} → (w w' : Ret-whnf cf)
                  → Σ[ e ∈ Ret-whnf.state w ≡ Ret-whnf.state w' ]
                      (ret-ticks w ≡ ret-ticks w')

  op-whnf-unique : ∀ {A ε} {cf : Config (A ‼ ε)} → (w w' : Op-whnf cf)
                 → Σ[ e ∈ Op-whnf.oper w ≡ Op-whnf.oper w' ]
                     (op-ticks w ≡ op-ticks w')
