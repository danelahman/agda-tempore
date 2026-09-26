------------------------------------------------------------------------
-- Running a grade's decision procedure, shared by the worked dense-    --
-- time instances.                                                      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Time.Dense.Decide where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

module Decide (G : Grade) where
  open Grade G

  ≾! : {c d : Carrier} {p : True (c ≾? d)} → c ≾ d
  ≾! {p = p} = toWitness p

  ⋠! : {c d : Carrier} {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! {p = p} = toWitnessFalse p
