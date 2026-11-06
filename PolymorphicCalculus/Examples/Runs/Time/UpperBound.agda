------------------------------------------------------------------------
-- Runs at upper bounds                                               --
--                                                                    --
-- A deadline is established at the top, and refuted at a grade below --
-- its delay and at one above it. `stretch` is refuted.               --
------------------------------------------------------------------------

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-UpperBound)

module PolymorphicCalculus.Examples.Runs.Time.UpperBound where

open Time-UpperBound using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Runs spec hints enum

------------------------------------------------------------------
-- 1. Deadlines

-- at the top: `ε₀ = ⊤` is a closed instance

deadline-top-verdict : verdict (check [] (deadline-top 1)) ≡ established
deadline-top-verdict = refl

deadline-top-typable : Typable [] (deadline-top 1)
deadline-top-typable = check-typable [] (deadline-top 1) deadline-top-verdict

-- below the delay: refuted, as `τ` is not below `c`

deadline-short-verdict : infer [] (deadline-at 2 1) ≡ untypable
deadline-short-verdict = refl

deadline-short-not-typable : ¬ Typable [] (deadline-at 2 1)
deadline-short-not-typable = infer-untypable [] (deadline-at 2 1) deadline-short-verdict

-- above the delay: the least `ε₀` is the top, and `⊤ ≾ ⌜ 3 ⌝` is false

deadline-long-verdict : infer [] (deadline-at 1 3) ≡ untypable
deadline-long-verdict = refl

deadline-long-not-typable : ¬ Typable [] (deadline-at 1 3)
deadline-long-not-typable = infer-untypable [] (deadline-at 1 3) deadline-long-verdict

------------------------------------------------------------------
-- 2. A handler calling the result of its resumption: refuted at a
-- candidate grade

stretch-verdict : infer [] (stretch 1) ≡ untypable
stretch-verdict = refl

stretch-not-typable : ¬ Typable [] (stretch 1)
stretch-not-typable = infer-untypable [] (stretch 1) stretch-verdict
