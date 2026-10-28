--------------------------------------------------------------------
-- The languages the inference examples run in                    --
--                                                                --
-- The sensor node's language (`Language.Examples.SensorNode`) at --
-- four grades, each with its `opTime` of                         --
-- `Grades.Examples.Worked.Operations.Grading`, as in the typing  --
-- examples, together covering the four combinations of the two   --
-- properties the solver reads from a grade:                      --
--                                                                --
--   grade                      u-least?   ·-comm?                --
--   Time/RightSided            yes        yes                    --
--   Time/LeftSided             no         yes                    --
--   Traces/Timed/RightSided    yes        no                     --
--   Traces/Timed/LeftSided     no         no                     --
--                                                                --
-- and at the two products of time with a security level, each    --
-- operation graded by its time and the level it touches          --
-- (`Worked/Operations/Footprint.agda`): at least `fast` ticks on --
-- the left, as in `Grading.Product-LeftSidedTimeLevel`, at most  --
-- `slow` on the right.                                           --
--                                                                --
-- At dense time, the right-sided grade takes the measured        --
-- figures of `Grading.Time-Dense-RightSided`, and the left-sided --
-- one the figures of `Grading.Time-LeftSided` read in dense      --
-- time.                                                          --
--                                                                --
-- The operations are the same at every grade, and so is their    --
-- enumeration.                                                   --
--                                                                --
-- The candidate values of a rigid that retry tries: at time, the --
-- bounds `0, …, s+1` for constants summing to `s` (at dense      --
-- time, a grid of fractions); at the products, the pairs of the  --
-- time candidates with both levels; at the timed traces, none.   --
--------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import Util.Equality

open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import Grades.Examples.System.Identity using (noWitnesses)
open import Grades.Product using (_×ʷ_)
import Grades.Examples.Worked.Operations.Grading as Grading

module OpenCalculus.Examples.Specs where

-- The sensor alphabet, enumerated

sensor-ops : List Op
sensor-ops = read ∷ write ∷ send ∷ []

sensor-complete : (op : Op) → op ∈ sensor-ops
sensor-complete read  = here refl
sensor-complete write = there (here refl)
sensor-complete send  = there (there (here refl))

module Time-RightSided where

  open import Grades.Examples.Time.RightSided using (right-sided-intervals; right-sided-witnesses)
  open Grading.Time-RightSided using (opTime)
  open import Language.Examples.SensorNode.Identity right-sided-intervals opTime right-sided-witnesses
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Time-LeftSided where

  open import Grades.Examples.Time.LeftSided using (left-sided-intervals; left-sided-witnesses)
  open Grading.Time-LeftSided using (opTime)
  open import Language.Examples.SensorNode.Identity left-sided-intervals opTime left-sided-witnesses
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Timed-RightSided where

  open import Grades.Examples.Worked.Traces.Timed.RightSided using (right-sided)
  open Grading.Traces-Timed-RightSided using (opTime)
  open import Language.Examples.SensorNode.Identity right-sided opTime noWitnesses
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Timed-LeftSided where

  open import Grades.Examples.Worked.Traces.Timed.LeftSided using (left-sided)
  open Grading.Traces-Timed-LeftSided using (opTime)
  open import Language.Examples.SensorNode.Identity left-sided opTime noWitnesses
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-LeftSidedTimeLevel where

  open import Grades.Examples.Product.LeftSidedTimeLevel using (left-sided-time×low-high)
  open import Grades.Examples.Time.LeftSided using (left-sided-witnesses)
  open import Grades.Examples.SecurityLevel using (low-high-witnesses)
  open Grading.Product-LeftSidedTimeLevel using (opTime)
  open import Language.Examples.SensorNode.Identity left-sided-time×low-high opTime
    (left-sided-witnesses ×ʷ low-high-witnesses)
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-RightSidedTimeLevel where

  open import Data.Product using (_×_; _,_)
  open import Grades.Examples.Product.RightSidedTimeLevel using (right-sided-time×low-high)
  open import Grades.Examples.Time.RightSided using (𝕀ᵣ; [0,_]; ↑_; right-sided-witnesses)
  open import Grades.Examples.SecurityLevel using (LowHigh; low-high-witnesses)
  open import Grades.Examples.Worked.Operations using (slow)
  open import Grades.Examples.Worked.Operations.Footprint using (touches)

  -- the time an operation may take at worst, and the level it touches

  opTime : Op → 𝕀ᵣ × LowHigh
  opTime o = ([0, ↑ slow o ] , touches o)

  open import Language.Examples.SensorNode.Identity right-sided-time×low-high opTime
    (right-sided-witnesses ×ʷ low-high-witnesses)
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Dense-Time-RightSided where

  open import Grades.Examples.Time.Dense.RightSided
    using (dense-right-sided-intervals; dense-right-sided-witnesses)
  open Grading.Time-Dense-RightSided using (opTime)
  open import Language.Examples.SensorNode.Identity dense-right-sided-intervals opTime
    dense-right-sided-witnesses
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Dense-Time-LeftSided where

  open import Grades.Base using (GradeMorphism)
  open import Grades.Examples.Time.Dense.LeftSided
    using (𝕀; dense-left-sided-intervals; dense-left-sided-witnesses; left-sided→dense)
  module Discrete = Grading.Time-LeftSided

  -- the discrete figures, read in dense time

  opTime : Op → 𝕀
  opTime o = GradeMorphism.map left-sided→dense (Discrete.opTime o)

  open import Language.Examples.SensorNode.Identity dense-left-sided-intervals opTime
    dense-left-sided-witnesses
    using (spec) public
  open import OpenCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete
