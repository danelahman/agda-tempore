open import Syntax.Grades
open import OperationalSemantics.TopLevelOpSemantics

module OperationalSemantics.TopLevelProgressTheorem (Grades : GradeSystem) (OpSemantics : TopLevelOpSemantics Grades) where

open GradeSystemInterface Grades
open TopLevelOpSemantics OpSemantics

open import OperationalSemantics.State (Grades)
open import OperationalSemantics.PreservationTheorem (Grades)
open import OperationalSemantics.TopLevelPreservationTheorem (Grades) (OpSemantics)

open import Syntax.Contexts (Grades)
open import Syntax.Language (Grades)
open import Syntax.Types (Grades)

open import Data.Empty
open import Util.Equality
open import Util.Operations (Grades)

-- Progress theorem at the top-level: a term is just a returned value or makes a reduction step.

data TopLevelProgresses : {ε : E}
                        → {S : 𝕊 []}
                        → {A : VType}
                        → (M : toCtx S ⊢C⦂ A ‼ ε)
                        → Set where

  is-top-level-value : {S : 𝕊 []}
                     → {A : VType}
                     → {V : toCtx S ⊢V⦂ A}
                       -----------------------------
                     → TopLevelProgresses (return V)

  top-level-steps    : ∀ {ε ε'}
                     → {A : VType}
                     → {S S' : 𝕊 []}
                     → {M : toCtx S ⊢C⦂ A ‼ ε}
                     → {M' : toCtx S' ⊢C⦂ A ‼ ε'}
                     → (prf : state-grade S' ·ᵣ mapᵉ ε' ≾ᵣ state-grade S ·ᵣ mapᵉ ε)
                     → ⟨ S , M ⟩ ⟿ ⟨ S' , M' ⟩
                       ------------------------------------------------------------
                     → TopLevelProgresses M

-- TODO: top-level progress theorem statement + proof
