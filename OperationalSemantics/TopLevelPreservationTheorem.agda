open import Syntax.Grades
open import OperationalSemantics.TopLevelOpSemantics

module OperationalSemantics.TopLevelPreservationTheorem (Grades : GradeSystem) (OpSemantics : TopLevelOpSemantics Grades) where

open GradeSystemInterface Grades
open TopLevelOpSemantics OpSemantics

open import OperationalSemantics.State (Grades)
open import OperationalSemantics.PreservationTheorem (Grades)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Renamings (Grades)
open import Syntax.RenActions (Grades)
open import Syntax.Substitutions (Grades)
open import Syntax.Types (Grades)

open import Data.Product

open import Relation.Binary.PropositionalEquality  as Eq hiding ( [_] ) 

open import Util.Operations (Grades)

-- Top-level small-step operational semantics aka Preservation theorem
--
-- Note: This top-level semantics uses the pure semantics of algebraic operations

data _⟿_ :  {C D : CType} → Config C → Config D → Set where

  -- Step according to the ordinary small-step semantics
  ↝-STEP : ∀ {A B ε ε'}
         → {S S' : 𝕊 []}
         → {M : (toCtx S ⊢C⦂ A ‼ ε)}
         → {N : (toCtx S' ⊢C⦂ B ‼ ε')}
         → ⟨ S , M ⟩ ↝ ⟨ S' , N ⟩
         → ⟨ S , M ⟩ ⟿ ⟨ S' , N ⟩

  -- Run a top-level implementation of an algebraic operation
  OP-STEP : ∀ {A ε op}
          → {S : 𝕊 []} 
          → {V : (toCtx S) ⊢V⦂ type-of-gtype (param op)} 
          → {M : toCtx S ⟨ mapᵉ (op-grade op) ⟩ ∷ type-of-gtype (arity op) ⊢C⦂ A ‼ ε} 
          → ⟨ S , perform op V M ⟩ ⟿
            ⟨ grade-pass S (mapᵉ (op-grade op)) , M [ Hd ↦ op-sem op V ]c ⟩

-- TODO: Needs an invariant lemma about how the states and effects are related before and after steps

-- TODO: Also needs a top-level version of the progress theorem (in a separate TopLevelProgress.agda file)
