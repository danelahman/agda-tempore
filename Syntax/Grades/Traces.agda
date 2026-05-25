--------------------------
-- Traces of operations --
--------------------------

open import Syntax.Grades
open import Syntax.Grades.TwoSidedIntervals
open import Syntax.LanguageSpec
open import Syntax.Operations

open import Util.Equality

module Syntax.Grades.Traces (S : LanguageSpec) where

open LanguageSpec S
open GradeSystemInterface Grades
open Operations Ops

data Trace : E → Set where
  [_]    : (op : Op) → Trace (op-grade op)
  _∷_    : ∀ {e} → (Trace e) → (op : Op) → Trace (e ·ₑ op-grade op)
  refine : ∀ {e} → (op : Op) → Trace e → op-grade op ≡ e → Trace (op-grade op)

infixl 5 _∷_
