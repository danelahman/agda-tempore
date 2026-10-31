------------------------------------------------------------------------
-- The language of the sensor node, over a grade system.              --
--                                                                    --
-- The base types and the operation signature of the typing and       --
-- inference examples: the grade system `S` and the effect grade      --
-- `opTime` assigns to each operation vary. `SensorNode.Identity` is  --
-- the instance at an identity grade system.                          --
--                                                                    --
-- There are two base types, differing in eternality: a `reading` is  --
-- the value of the sensor at the moment it was taken, and a `nodeid` --
-- is the identifier of the node.                                     --
------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Data.Nat.Base using (ℕ) renaming (_<_ to _<ℕ_)
import Data.Nat.Properties as ℕₚ
open import Data.Unit using (⊤; tt)

open import Relation.Nullary using (Dec; yes; no)

open import Grades.Base
open import Language.BaseTypes
open import Language.Operations
open import Language.Spec

open import Grades.Examples.Worked.Operations
  using (Op; read; write; send; _≟ₒ_)

open import Util.Equality

module Language.Examples.SensorNode
  (S : GradeSystem) (opTime : Op → Grade.Carrier (GradeSystem.EGrade S)) where

------------------------------------------------------------------------
-- The grades

grades : GradeSystem
grades = S

open GradeSystemInterface grades public

------------------------------------------------------------------------
-- Base types
--
-- A reading is the sensor's value at the moment it was taken, so it is
-- not eternal; the node's identifier is.

data BT : Set where
  reading : BT
  nodeid  : BT

_≡ᴮ?_ : (b b' : BT) → Dec (b ≡ b')
reading ≡ᴮ? reading = yes refl
reading ≡ᴮ? nodeid  = no λ ()
nodeid  ≡ᴮ? reading = no λ ()
nodeid  ≡ᴮ? nodeid  = yes refl

EternalBT : BT → Set
EternalBT reading = ⊥
EternalBT nodeid  = ⊤

eternalBT? : (b : BT) → Dec (EternalBT b)
eternalBT? reading = no λ ()
eternalBT? nodeid  = yes tt

baseTypes : BaseTypes
baseTypes = record
  { BaseType         = BT
  ; _≡ᵇ?_            = _≡ᴮ?_
  ; EternalBaseType  = EternalBT
  ; eternalBaseType? = eternalBT?
  ; BaseConstants    = λ _ → ℕ
  ; _≺ᵇ_                  = _<ℕ_
  ; ≺ᵇ-isStrictTotalOrder = λ _ → ℕₚ.<-isStrictTotalOrder
  }

open import Language.GroundTypes grades baseTypes

------------------------------------------------------------------------
-- The operation signature
--
-- `read` takes nothing and produces a reading; `write` and `send` each
-- consume one and produce nothing. `opTime` grades them.

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
    param' read  = unit
    param' write = Base reading
    param' send  = Base reading

    arity' : Op → GType
    arity' read  = Base reading
    arity' write = unit
    arity' send  = unit

spec : LanguageSpec
spec = record
  { Grades = grades
  ; BTs    = baseTypes
  ; Ops    = operations
  }

open Operations operations public using (param; arity; op-grade)
