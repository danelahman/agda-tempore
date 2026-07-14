open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Monad

module OperationalSemantics.TopLevelOpSemantics (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

open import OperationalSemantics.PreservationTheorem S
open import OperationalSemantics.State                S

open import Syntax.Contexts S
open import Syntax.Language S
open import Syntax.Types    S

-- TopLevel pure semantics of algebraic operations

record TopLevelOpSemantics : Set where
  field 
    op-sem : (op : Op)
           → {S : 𝕊 []} -- TODO: formally requires a naturality condition; needs to be parametric in S
           → toCtx S ⊢V⦂ type-of-gtype (param op)
           → toCtx S ⟨ mapᵉ (op-grade op) ⟩ ⊢V⦂ type-of-gtype (arity op)

-- TopLevel monadic semantics of algebraic operations
--
-- The implementation runs in a graded monad over the effect grades, and its
-- grade is the operation's declared duration: running `mon-op-sem op V` costs
-- `op-grade op` worth of time, which is the same time the reduction rule locks
-- into the state. The arity value it returns is available only after that time
-- has passed, hence the `⟨ mapᵉ (op-grade op) ⟩` in its context.

record TopLevelMonadicOpSemantics (monad : GradedMonad EGrade) : Set₁ where
  open GradedMonad monad

  field
    mon-op-sem : (op : Op)
               → {S : 𝕊 []} -- TODO: formally requires a naturality condition; needs to be parametric in S
               → toCtx S ⊢V⦂ type-of-gtype (param op)
               → T (op-grade op)
                   (toCtx S ⟨ mapᵉ (op-grade op) ⟩ ⊢V⦂ type-of-gtype (arity op))
