--------------------------------------------------------------------
-- The languages the inference examples run in                    --
--                                                                --
-- The sensor node's language of `Worked/Typing/Core.agda` at     --
-- four grades, each with the `opTime` of its `Worked/Typing`     --
-- instance, together covering the four combinations of the two   --
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
-- the left, as in `Worked/Typing/Product/LeftSidedTimeLevel`, at --
-- most `slow` on the right.                                      --
--                                                                --
-- The operations are the same at every grade, and so is their    --
-- enumeration.                                                   --
--------------------------------------------------------------------

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations using (Op; read; write; send)

module TypeInference.Examples.Specs where

-- The sensor alphabet, enumerated

sensor-ops : List Op
sensor-ops = read ∷ write ∷ send ∷ []

sensor-complete : (op : Op) → op ∈ sensor-ops
sensor-complete read  = here refl
sensor-complete write = there (here refl)
sensor-complete send  = there (there (here refl))

module Time-RightSided where

  open import Syntax.Grades.Example.Time.RightSided using (right-sided-intervals)
  open import Syntax.Grades.Example.Worked.Typing.Time.RightSided using (opTime)
  open import Syntax.Grades.Example.Worked.Typing.Core right-sided-intervals opTime
    using (spec) public
  open import TypeInference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Time-LeftSided where

  open import Syntax.Grades.Example.Time.LeftSided using (left-sided-intervals)
  open import Syntax.Grades.Example.Worked.Typing.Time.LeftSided using (opTime)
  open import Syntax.Grades.Example.Worked.Typing.Core left-sided-intervals opTime
    using (spec) public
  open import TypeInference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Timed-RightSided where

  open import Syntax.Grades.Example.Worked.Traces.Timed.RightSided using (right-sided)
  open import Syntax.Grades.Example.Worked.Typing.Traces.Timed.RightSided using (opTime)
  open import Syntax.Grades.Example.Worked.Typing.Core right-sided opTime
    using (spec) public
  open import TypeInference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Traces-Timed-LeftSided where

  open import Syntax.Grades.Example.Worked.Traces.Timed.LeftSided using (left-sided)
  open import Syntax.Grades.Example.Worked.Typing.Traces.Timed.LeftSided using (opTime)
  open import Syntax.Grades.Example.Worked.Typing.Core left-sided opTime
    using (spec) public
  open import TypeInference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-LeftSidedTimeLevel where

  open import Syntax.Grades.Example.Product.LeftSidedTimeLevel using (left-sided-time×low-high)
  open import Syntax.Grades.Example.Worked.Typing.Product.LeftSidedTimeLevel using (opTime)
  open import Syntax.Grades.Example.Worked.Typing.Core left-sided-time×low-high opTime
    using (spec) public
  open import TypeInference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete

module Product-RightSidedTimeLevel where

  open import Data.Product using (_×_; _,_)
  open import Syntax.Grades.Example.Product.RightSidedTimeLevel using (right-sided-time×low-high)
  open import Syntax.Grades.Example.Time.RightSided using (𝕀ᵣ; [0,_]; ↑_)
  open import Syntax.Grades.Example.SecurityLevel using (LowHigh)
  open import Syntax.Grades.Example.Worked.Operations using (slow)
  open import Syntax.Grades.Example.Worked.Operations.Footprint using (touches)

  -- the time an operation may take at worst, and the level it touches

  opTime : Op → 𝕀ᵣ × LowHigh
  opTime o = ([0, ↑ slow o ] , touches o)

  open import Syntax.Grades.Example.Worked.Typing.Core right-sided-time×low-high opTime
    using (spec) public
  open import TypeInference.SolverImpl.Enum spec using (OpEnum; opEnum)

  enum : OpEnum
  enum = opEnum sensor-ops sensor-complete
