------------------------------------------------------------------------
-- A grade system in which the resource grades keep only the floor.    --
--                                                                     --
-- The mixed column's counterpart of                                   --
-- `System.TraceIntervalsToTraceSets`. Effect grades are the mixed      --
-- two-sided trace intervals, bounding every run of a computation from  --
-- both sides; resource grades are the Smyth-lift floors of             --
-- `Traces.UpperLift.LeftSided`, which is the mixed grade's own lower   --
-- endpoint read alone. The projection forgets the cap, so a resource   --
-- grade says only what every run is guaranteed to have done, not what  --
-- it is forbidden from doing.                                          --
--                                                                     --
-- This is the projection a box modality wants from these grades: the   --
-- premise `ρ' ≾ᵣ ρ` of `unbox` then reads "whatever elapsed, it met    --
-- one of the demands `ρ` lists", those being read disjunctively.       --
--                                                                     --
-- As in the sibling systems, monotonicity is the first component of    --
-- the interval order and the monoid laws hold on the nose, the product --
-- being computed endpoint by endpoint.                                 --
------------------------------------------------------------------------

open import Data.Nat.Base using (ℕ)
open import Data.Product using (proj₁)

open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.Example.System.MixedTraceIntervalsToTraceSets (S : LanguageSpec) where

open LanguageSpec S
open Operations Ops

-- The construction is parameterised by an assignment of a predetermined
-- execution time to each operation symbol, which both endpoints' order
-- is read against.

module _ (opTime : Op → ℕ) where

  open import Syntax.Grades.Example.Traces.Subtrace.Mixed.TwoSided Op _≟ₒ_ opTime
    using (mixed-two-sided; lo)
  open import Syntax.Grades.Example.Traces.Subtrace.UpperLift.LeftSided Op _≟ₒ_ opTime
    using (upper-lift-left-sided)

  -- the projection reads off the floor

  mixed-trace-intervals→traces : mixed-two-sided →ᵍ upper-lift-left-sided
  mixed-trace-intervals→traces = record
    { map          = lo
    ; map-monotone = proj₁
    ; map-u        = refl
    ; map-·        = refl
    ; map-of-nat   = refl
    }

  mixedTraceIntervalsToTraceSetsGradeSystem : GradeSystem
  mixedTraceIntervalsToTraceSetsGradeSystem = record
    { RGrade = upper-lift-left-sided
    ; EGrade = mixed-two-sided
    ; ∣_∣ᵉ   = mixed-trace-intervals→traces
    }
