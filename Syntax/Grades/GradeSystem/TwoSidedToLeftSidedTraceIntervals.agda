-------------------------------------------------------------------------------
-- Example grade system of two-sided trace intervals as effect grades and    --
-- one-sided trace intervals as resource grades (for a subset of operations) --
-------------------------------------------------------------------------------

open import Data.Bool
open import Data.List
open import Data.Product
open import Data.Unit using (tt)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.GradeSystem.TwoSidedToLeftSidedTraceIntervals (S : LanguageSpec) where

open Grade
open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

module _ (OpPred : Op → Bool) where

  -- the restriction of traces to the sub-alphabet picked out by `OpPred`

  open import Syntax.Grades.Traces.Restriction Op _≟ₒ_ OpPred

  -- the two-sided traces (over all operations) provide the effect grades, the
  -- left-sided traces (over `OpPred` operation) the resource grades

  open import Syntax.Grades.Traces.TwoSidedTraces Op _≟ₒ_
  open import Syntax.Grades.Traces.LeftSidedTraces Op' _≟ₒ'_

  open import Syntax.Grades.Traces.Base

  tst→lst : two-sided-traces →ᵍ left-sided-traces
  tst→lst = record
    { map = λ { [ neTraces lower nonempty , upper , lo⊑up ] →
        [ neTraces (restrict-traces lower) (restrict-nonempty nonempty) ,⊤⟩ }
    ; map-monotone = λ I≾J → restrict-⊑ (proj₁ I≾J)
    ; map-u = refl
    ; map-· = λ {I} {J} →
        cong [_,⊤⟩ (ne-ext Op'
          (restrict-·ˢ (traces (TraceInterval.lower I))
                       (traces (TraceInterval.lower J))))
    ; map-of-nat = λ {n} → cong (λ z → [ neTraces (z ∷ []) tt ,⊤⟩) (restrict-⟨⟩ n)
    }
