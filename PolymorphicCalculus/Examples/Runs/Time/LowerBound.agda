------------------------------------------------------------------------
-- Runs at lower bounds                                               --
--                                                                    --
-- A deadline is established at the top, and refuted at a grade below --
-- its delay and at one above it. `stretch` is established.           --
------------------------------------------------------------------------

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-LowerBound)

module PolymorphicCalculus.Examples.Runs.Time.LowerBound where

open Time-LowerBound using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Runs spec hints enum

------------------------------------------------------------------
-- 1. Deadlines

deadline-top-verdict : verdict (check [] (deadline-top 1)) ≡ established
deadline-top-verdict = refl

deadline-top-typable : Typable [] (deadline-top 1)
deadline-top-typable = check-typable [] (deadline-top 1) deadline-top-verdict

deadline-short-verdict : infer [] (deadline-at 2 1) ≡ untypable
deadline-short-verdict = refl

deadline-short-not-typable : ¬ Typable [] (deadline-at 2 1)
deadline-short-not-typable = infer-untypable [] (deadline-at 2 1) deadline-short-verdict

deadline-long-verdict : infer [] (deadline-at 1 3) ≡ untypable
deadline-long-verdict = refl

deadline-long-not-typable : ¬ Typable [] (deadline-at 1 3)
deadline-long-not-typable = infer-untypable [] (deadline-at 1 3) deadline-long-verdict

------------------------------------------------------------------
-- 2. A handler calling the result of its resumption

stretch-verdict : verdict (check [] (stretch 1)) ≡ established
stretch-verdict = refl

stretch-typable : Typable [] (stretch 1)
stretch-typable = check-typable [] (stretch 1) stretch-verdict
