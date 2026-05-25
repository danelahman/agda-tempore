open import Syntax.Grades
open import Util.BaseTypes

module OperationalSemantics.TopLevelOpSemantics (Grades : GradeSystem) (BTs : BaseTypes) where

open GradeSystemInterface Grades

open import OperationalSemantics.State (Grades) (BTs)
open import OperationalSemantics.PreservationTheorem (Grades) (BTs)

open import Syntax.Contexts (Grades) (BTs)
open import Syntax.Language (Grades) (BTs)
open import Syntax.Types (Grades) (BTs)

open import Util.Monad
open import Util.Operations (Grades) (BTs)

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
