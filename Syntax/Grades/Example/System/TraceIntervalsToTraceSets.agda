------------------------------------------------------------------------
-- A grade system in which the resource grades keep only the floor.    --
--                                                                     --
-- The trace-level counterpart of                                      --
-- `System.IntervalsToLeftSidedIntervals`. Effect grades are two-sided  --
-- trace intervals, bounding a computation's runs from both sides;      --
-- resource grades are the one-sided trace grades of                    --
-- `Traces.LowerLift.LeftSided`, which keeps the floor alone. The        --
-- projection forgets the cap, so a resource grade says only what a     --
-- computation is guaranteed to have done, not what it is forbidden     --
-- from doing.                                                          --
--                                                                     --
-- As there, monotonicity is the first component of the interval order  --
-- and the monoid laws hold on the nose, the product being computed     --
-- endpoint by endpoint.                                                --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.Example.System.TraceIntervalsToTraceSets (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

-- The construction is parameterised by an assignment of a predetermined
-- execution time to each operation symbol, which both endpoints' order
-- is read against.

module _ (opTime : Op → ℕ) where

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.TwoSided Op _≟ₒ_ opTime
    using (lower-lift-two-sided; lo)
  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.LeftSided Op _≟ₒ_ opTime
    using (lower-lift-left-sided)

  -- the projection reads off the floor

  trace-intervals→traces : lower-lift-two-sided →ᵍ lower-lift-left-sided
  trace-intervals→traces = record
    { map          = lo
    ; map-monotone = proj₁
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  traceIntervalsToTraceSetsGradeSystem : GradeSystem
  traceIntervalsToTraceSetsGradeSystem = record
    { RGrade = lower-lift-left-sided
    ; EGrade = lower-lift-two-sided
    ; ∣_∣ᵉ   = trace-intervals→traces
    }
