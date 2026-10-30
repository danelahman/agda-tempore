------------------------------------------------------------------
-- Runs at right-sided intervals                                --
--                                                              --
-- A budget at the top is established, at any finite grade      --
-- refuted; `stretch` is refuted.                               --
------------------------------------------------------------------

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)

module PolymorphicCalculus.Examples.Runs.Time.RightSided where

open Time-RightSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Runs spec hints enum

------------------------------------------------------------------
-- 1. Budgets

-- at the top: `ε₀ = ⊤` is a closed instance

budget-top-verdict : verdict (check [] (budget-top 1)) ≡ established
budget-top-verdict = refl

budget-top-typable : Typable [] (budget-top 1)
budget-top-typable = check-typable [] (budget-top 1) budget-top-verdict

-- below the delay: refuted through the factor edge

budget-short-verdict : infer [] (budget-at 2 1) ≡ untypable
budget-short-verdict = refl

budget-short-not-typable : ¬ Typable [] (budget-at 2 1)
budget-short-not-typable = infer-untypable [] (budget-at 2 1) budget-short-verdict

-- above the delay: `ε₀` is lowered to the top, and `⊤ ≾ ⌜ 3 ⌝` is false

budget-long-verdict : infer [] (budget-at 1 3) ≡ untypable
budget-long-verdict = refl

budget-long-not-typable : ¬ Typable [] (budget-at 1 3)
budget-long-not-typable = infer-untypable [] (budget-at 1 3) budget-long-verdict

------------------------------------------------------------------
-- 2. A handler calling the result of its resumption: refuted at a
-- witness

stretch-verdict : infer [] (stretch 1) ≡ untypable
stretch-verdict = refl

stretch-not-typable : ¬ Typable [] (stretch 1)
stretch-not-typable = infer-untypable [] (stretch 1) stretch-verdict
