------------------------------------------------------------------------
-- Example: traces for the grade system where effects' grades are TSI --
-- and resources' grades are LSI.                                     --
------------------------------------------------------------------------

module Syntax.Grades.Examples.ExampleTSILSI where

open import Data.Nat.Base

open import Syntax.Grades
open import Syntax.Grades.IntGradeSystem
open import Syntax.Grades.Traces (intGradeSystem)
open import Syntax.Grades.TwoSidedIntervals

open import Util.Equality
open import Util.Operations (intGradeSystem)

-- Operations:
postulate
  clean  : Op
  primer : Op
  paint  : Op

-- Refinement of some of the operations:
postulate
  pick-cleaning-materials   : Op
  cleaning-process          : Op
  return-cleaning-materials : Op

-- Operations' grades:
postulate
  grade-clean  : op-grade clean  ≡ [ 2 , 5 ]tsi (s≤s (s≤s z≤n))
  grade-primer : op-grade primer ≡ [ 1 , 1 ]tsi (s≤s z≤n)
  grade-paint  : op-grade paint  ≡ [ 3 , 9 ]tsi (s≤s (s≤s (s≤s z≤n)))

  grade-pick-cleaning-materials   : op-grade pick-cleaning-materials   ≡ [ 0 , 1 ]tsi z≤n
  grade-cleaning-process          : op-grade cleaning-process          ≡ [ 2 , 3 ]tsi (s≤s (s≤s z≤n))
  grade-return-cleaning-materials : op-grade return-cleaning-materials ≡ [ 0 , 1 ]tsi z≤n

example-trace₁ : Trace ((op-grade clean ·ᵢ op-grade primer) ·ᵢ op-grade paint)
example-trace₁ = [ clean ] ∷ primer ∷ paint

-- Clean subtrace
clean-subtrace : Trace ((op-grade pick-cleaning-materials ·ᵢ op-grade cleaning-process) ·ᵢ (op-grade return-cleaning-materials))
clean-subtrace = [ pick-cleaning-materials ] ∷ cleaning-process ∷ return-cleaning-materials

-- The grade of the clean operation coincides with the grade of its refinement operations
clean≡subtrace : op-grade clean ≡ op-grade pick-cleaning-materials ·ᵢ op-grade cleaning-process ·ᵢ op-grade return-cleaning-materials
clean≡subtrace =
  trans
    grade-clean
    (trans
      (eqᵢ refl refl)
      (sym
        (cong₂
          _·ᵢ_
          (cong₂ _·ᵢ_ grade-pick-cleaning-materials grade-cleaning-process)
          grade-return-cleaning-materials)))

refine-write : Trace (op-grade clean)
refine-write = refine clean clean-subtrace clean≡subtrace
