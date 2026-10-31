--------------------------------------------------------------------
-- The languages the inference examples run in                    --
--                                                                --
-- The sensor node's language (`Language.Examples.SensorNode`)    --
-- with the operation times of `Worked.Operations.Grading`, at    --
-- four grades covering the hint properties the solver reads:     --
--                                                                --
--   grade                      𝟏-least?   ·-comm?                --
--   Time/RightSided            yes        yes                    --
--   Time/LeftSided             no         yes                    --
--   Traces/Timed/RightSided    yes        no                     --
--   Traces/Timed/LeftSided     no         no                     --
--                                                                --
-- and at time paired with a security level (`Footprint`) and at  --
-- dense time on both sides. Hints are `identityʰ`; retry's       --
-- candidates are, at time, the bounds `0, …, s+1` for constants  --
-- summing to `s` (a grid at dense time), at the products these   --
-- paired with both levels, at the timed traces none.             --
--------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import Util.Equality

open import Grades.Hints using (SystemHints; noGradeHints)
open import Grades.Examples.Worked.Operations using (Op; read; write; send)
open import Grades.Examples.System.Identity using (identityʰ; noWitnesses)
open import Grades.Product using (_×ʷ_)
open import Language.Spec using (LanguageSpec)
import Grades.Examples.Worked.Operations.Grading as Grading

module PolymorphicCalculus.Examples.Specs where

-- The sensor alphabet, enumerated

sensor-ops : List Op
sensor-ops = read ∷ write ∷ send ∷ []

sensor-complete : (op : Op) → op ∈ sensor-ops
sensor-complete read  = here refl
sensor-complete write = there (here refl)
sensor-complete send  = there (there (here refl))

module Time-RightSided where

  open import Grades.Examples.Time.RightSided
    using (right-sided-intervals; right-sided-intervalsʰ; right-sided-witnesses)
  open Grading.Time-RightSided using (opTime)
  open import Language.Examples.SensorNode.Identity right-sided-intervals opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ right-sided-intervalsʰ right-sided-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Time-LeftSided where

  open import Grades.Examples.Time.LeftSided
    using (left-sided-intervals; left-sided-intervalsʰ; left-sided-witnesses)
  open Grading.Time-LeftSided using (opTime)
  open import Language.Examples.SensorNode.Identity left-sided-intervals opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ left-sided-intervalsʰ left-sided-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Timed-RightSided where

  open import Grades.Examples.Worked.Traces.Timed.RightSided using (right-sided; right-sidedʰ)
  open Grading.Traces-Timed-RightSided using (opTime)
  open import Language.Examples.SensorNode.Identity right-sided opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ right-sidedʰ noWitnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Timed-LeftSided where

  open import Grades.Examples.Worked.Traces.Timed.LeftSided using (left-sided)
  open Grading.Traces-Timed-LeftSided using (opTime)
  open import Language.Examples.SensorNode.Identity left-sided opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ noGradeHints noWitnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-LeftSidedTimeLevel where

  open import Grades.Examples.Product.LeftSidedTimeLevel
    using (left-sided-time×low-high; left-sided-time×low-highʰ)
  open import Grades.Examples.Time.LeftSided using (left-sided-witnesses)
  open import Grades.Examples.SecurityLevel using (low-high-witnesses)
  open Grading.Product-LeftSidedTimeLevel using (opTime)
  open import Language.Examples.SensorNode.Identity left-sided-time×low-high opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ left-sided-time×low-highʰ (left-sided-witnesses ×ʷ low-high-witnesses)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-RightSidedTimeLevel where

  open import Data.Product using (_×_; _,_)
  open import Grades.Examples.Product.RightSidedTimeLevel
    using (right-sided-time×low-high; right-sided-time×low-highʰ)
  open import Grades.Examples.Time.RightSided using (𝕀ᵣ; [0,_]; ↑_; right-sided-witnesses)
  open import Grades.Examples.SecurityLevel using (LowHigh; low-high-witnesses)
  open import Grades.Examples.Worked.Operations using (slow)
  open import Grades.Examples.Worked.Operations.Footprint using (touches)

  -- the time an operation may take at worst, and the level it touches

  opTime : Op → 𝕀ᵣ × LowHigh
  opTime o = ([0, ↑ slow o ] , touches o)

  open import Language.Examples.SensorNode.Identity right-sided-time×low-high opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ right-sided-time×low-highʰ (right-sided-witnesses ×ʷ low-high-witnesses)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Dense-Time-RightSided where

  open import Grades.Examples.Time.Dense.RightSided
    using (dense-right-sided-intervals; dense-right-sided-intervalsʰ; dense-right-sided-witnesses)
  open Grading.Time-Dense-RightSided using (opTime)
  open import Language.Examples.SensorNode.Identity dense-right-sided-intervals opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ dense-right-sided-intervalsʰ dense-right-sided-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Dense-Time-LeftSided where

  open import Grades.Base using (GradeMorphism)
  open import Grades.Examples.Time.Dense.LeftSided
    using (𝕀; dense-left-sided-intervals; dense-left-sided-intervalsʰ; dense-left-sided-witnesses;
           left-sided→dense)
  module Discrete = Grading.Time-LeftSided

  -- the discrete figures, read in dense time

  opTime : Op → 𝕀
  opTime o = GradeMorphism.map left-sided→dense (Discrete.opTime o)

  open import Language.Examples.SensorNode.Identity dense-left-sided-intervals opTime
    using (spec) public
  open import PolymorphicCalculus.Inference.SolverImpl.Enum spec using (OpEnum; opEnum)

  hints : SystemHints (LanguageSpec.Grades spec)
  hints = identityʰ dense-left-sided-intervalsʰ dense-left-sided-witnesses

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete
