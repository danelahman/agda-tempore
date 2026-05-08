--------------------------
-- Traces of operations --
--------------------------

open import Syntax.Grades

module Syntax.Grades.Traces (Grades : GradeSystem) where

open GradeSystemInterface Grades

open import Syntax.Grades.TwoSidedIntervals

open import Util.Equality
open import Util.Operations (Grades)

data Trace : E → Set where
  [_]    : (op : Op) → Trace (op-grade op)
  _∷_    : ∀ {e} → (Trace e) → (op : Op) → Trace (e ·ₑ op-grade op)
  refine : ∀ {e} → (op : Op) → Trace e → op-grade op ≡ e → Trace (op-grade op)

infixl 5 _∷_
