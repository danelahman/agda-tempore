------------------------------------------------------------------------
-- Running a grade's decision procedure, shared by the worked dense-  --
-- time instances.                                                    --
------------------------------------------------------------------------

module Grades.Examples.Worked.Time.Dense.Decide where

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Durations using (Duration)
open import Grades.Base using (Grade)

module Decide {D : Duration} (G : Grade D) where
  open Grade G

  ≾! : {c d : Carrier} {p : True (c ≾? d)} → c ≾ d
  ≾! {p = p} = toWitness p

  ⋠! : {c d : Carrier} {p : False (c ≾? d)} → ¬ (c ≾ d)
  ⋠! {p = p} = toWitnessFalse p
