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

record TopLevelMonadicOpSemantics (monad : Monad) : Set₁ where
  open Monad monad
  
  field
    mon-op-sem : (op : Op)
               → {S : 𝕊 []} -- TODO: formally requires a naturality condition; needs to be parametric in S
               → toCtx S ⊢V⦂ type-of-gtype (param op)
               → T (toCtx S ⟨ mapᵉ (op-grade op) ⟩ ⊢V⦂ type-of-gtype (arity op))
