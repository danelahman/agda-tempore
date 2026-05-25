--------------------------
-- Traces of operations --
--------------------------

open import Syntax.Grades
open import Syntax.BaseTypes
open import Syntax.Operations

module Syntax.Grades.Traces
  (Grades : GradeSystem)
  (BTs    : BaseTypes)
  (Ops    : Operations Grades BTs)
  where

open GradeSystemInterface Grades

open import Syntax.Grades.TwoSidedIntervals

open import Util.Equality
open Operations Ops

data Trace : E → Set where
  [_]    : (op : Op) → Trace (op-grade op)
  _∷_    : ∀ {e} → (Trace e) → (op : Op) → Trace (e ·ₑ op-grade op)
  refine : ∀ {e} → (op : Op) → Trace e → op-grade op ≡ e → Trace (op-grade op)

infixl 5 _∷_
