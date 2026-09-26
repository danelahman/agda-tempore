------------------------------------------------------------------------
-- A language specification over the sensor-node alphabet.            --
--                                                                    --
-- The grade systems of `Syntax.Grades.Example.System.*` over a set   --
-- of operations take it as part of a `LanguageSpec`, which also      --
-- fixes base types and an operation signature. This module gives     --
-- that specification for the sensor node.                            --
--                                                                    --
-- Its grade system projects the two-sided intervals onto the         --
-- left-sided ones: effect grades bound the running time of a         --
-- computation from both sides, and resource grades keep the lower    --
-- bound. `op-grade` is `opTime`, the interval in which the execution --
-- time of each operation lies.                                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Spec where

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ)

open import Relation.Nullary using (yes; no)

open import Util.Equality

open import Syntax.BaseTypes
open import Syntax.Grades
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Syntax.Grades.Example.System.IntervalsToLeftSidedIntervals
  using (twoSidedIntervalsToLeftSidedIntervalsGradeSystem)

open import Syntax.Grades.Example.Worked.Operations

------------------------------------------------------------------------
-- The grades the node's own operations are graded in

grades : GradeSystem
grades = twoSidedIntervalsToLeftSidedIntervalsGradeSystem

------------------------------------------------------------------------
-- Base types
--
-- One base type, the sensor readings. A reading is not eternal: it is
-- the value of the sensor at the moment it was taken.

data BT : Set where
  reading : BT

baseTypes : BaseTypes
baseTypes = record
  { BaseType         = BT
  ; _≡ᵇ?_            = λ { reading reading → yes refl }
  ; EternalBaseType  = λ _ → ⊥
  ; eternalBaseType? = λ _ → no λ ()
  ; BaseConstants    = λ _ → ℕ
  }

open import Syntax.GroundTypes grades baseTypes

------------------------------------------------------------------------
-- The operation signature
--
-- `read` takes nothing and produces a reading; `write` and `send` each
-- consume one and produce nothing. Each is graded by the interval its
-- execution time falls in.

operations : Operations grades baseTypes
operations = record
  { Op       = Op
  ; _≟ₒ_     = _≟ₒ_
  ; param    = param'
  ; arity    = arity'
  ; op-grade = opTime
  }
  where
    param' : Op → GType
    param' read  = Unit
    param' write = Base reading
    param' send  = Base reading

    arity' : Op → GType
    arity' read  = Base reading
    arity' write = Unit
    arity' send  = Unit

------------------------------------------------------------------------
-- The specification

spec : LanguageSpec
spec = record
  { Grades = grades
  ; BTs    = baseTypes
  ; Ops    = operations
  }
