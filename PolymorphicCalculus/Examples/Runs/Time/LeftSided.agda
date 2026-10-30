------------------------------------------------------------------
-- Runs at left-sided intervals                                 --
--                                                              --
-- "At least `n` ticks": the unit is not least, so a budget is  --
-- refuted at every grade but the top, where it is established; --
-- a handler that stretches its resumption's result keeps its   --
-- deferred condition at every rigid and is established.        --
------------------------------------------------------------------

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-LeftSided)

module PolymorphicCalculus.Examples.Runs.Time.LeftSided where

open Time-LeftSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Runs spec hints enum

------------------------------------------------------------------
-- 1. Budgets

budget-top-verdict : verdict (check [] (budget-top 1)) ≡ established
budget-top-verdict = refl

budget-top-typable : Typable [] (budget-top 1)
budget-top-typable = check-typable [] (budget-top 1) budget-top-verdict

budget-short-verdict : infer [] (budget-at 2 1) ≡ untypable
budget-short-verdict = refl

budget-short-not-typable : ¬ Typable [] (budget-at 2 1)
budget-short-not-typable = infer-untypable [] (budget-at 2 1) budget-short-verdict

budget-long-verdict : infer [] (budget-at 1 3) ≡ untypable
budget-long-verdict = refl

budget-long-not-typable : ¬ Typable [] (budget-at 1 3)
budget-long-not-typable = infer-untypable [] (budget-at 1 3) budget-long-verdict

------------------------------------------------------------------
-- 2. A handler calling the result of its resumption

stretch-verdict : verdict (check [] (stretch 1)) ≡ established
stretch-verdict = refl

stretch-typable : Typable [] (stretch 1)
stretch-typable = check-typable [] (stretch 1) stretch-verdict
