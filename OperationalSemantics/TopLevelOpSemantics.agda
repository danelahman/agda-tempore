open import Syntax.Grades

module OperationalSemantics.TopLevelOpSemantics (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import OperationalSemantics.State (Grades)
open import OperationalSemantics.PreservationTheorem (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Types (Grades)

open import Util.Operations (Grades)

-- TopLevel pure semantics of algebraic operations

record TopLevelOpSemantics : Set where
  field 
    op-sem : (op : Op)
           → {S : 𝕊 []} -- TODO: formally requires a naturality condition; needs to be parametric in S
           → toCtx S ⊢V⦂ type-of-gtype (param op) → toCtx S ⟨ mapᵉ (op-grade op) ⟩ ⊢V⦂ type-of-gtype (arity op)
