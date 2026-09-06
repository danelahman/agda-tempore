------------------------------------------------------------------------
-- A language specification over the sensor-node alphabet.             --
--                                                                     --
-- `Syntax.Grades.Example.System.*` build a grade system over a set of  --
-- operation names, and take that set as part of a whole `LanguageSpec` --
-- -- so instantiating them means fixing base types and an operation    --
-- signature as well. This module does that once for the sensor node.   --
--                                                                     --
-- The spec's own grades are the two-sided intervals projected onto the --
-- left-sided ones: effect grades bound a computation's running time    --
-- from both sides, resource grades keep the lower bound. That makes    --
-- `op-grade` literally `opTime` -- the interval each operation's        --
-- execution time falls in -- which is what the whole development is    --
-- about, and it is the starting point the other grade systems below    --
-- offer alternatives to.                                              --
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
  { BaseType                   = BT
  ; _≡ᵇ?_                      = λ { reading reading → yes refl }
  ; EternalBaseType            = λ _ → ⊥
  ; eternalBaseType?           = λ _ → no λ ()
  ; eternalBaseType-irrelevant = λ ()
  ; BaseConstants              = λ _ → ℕ
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
