------------------------------------------------------------------------
-- Durations at upper bounds on rational time                         --
--                                                                    --
-- A box is a lease. Two delays of half a unit fill a lease of one    --
-- unit, and a half and a quarter fit in it; a half and three         --
-- quarters overrun it and are refused. A box argument claimed after  --
-- a half and a quarter is inferred as a lease of at least three      --
-- quarters.                                                          --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Util.NonNegativeRational
  using (_/_; #_; nonZero)

open import PolymorphicCalculus.Examples.Specs using (module Time-Rational-UpperBound)

module PolymorphicCalculus.Examples.Durations.Time.UpperBound where

open Time-Rational-UpperBound using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Durations spec hints enum

------------------------------------------------------------------
-- 1. A lease of one unit: claimed after two half units and after
-- a half and a quarter, not after a half and three quarters

claim-on-time-reported :
  schemeOf (infer [] (claim-after (# 1) (1 / 2) (1 / 2)))
  ≡ just (expected-claim-after (# 1))
claim-on-time-reported = refl

claim-on-time-derivable : Typable [] (claim-after (# 1) (1 / 2) (1 / 2))
claim-on-time-derivable = claim-after-typable (# 1) (1 / 2) (1 / 2) _

claim-early-reported :
  schemeOf (infer [] (claim-after (# 1) (1 / 2) (1 / 4)))
  ≡ just (expected-claim-after (3 / 4))
claim-early-reported = refl

-- the late claim fails its premise `[0, 5 / 4 ] ≾ [0, 1 ]`

claim-late-verdict : infer [] (claim-after (# 1) (1 / 2) (3 / 4)) ≡ untypable
claim-late-verdict = refl

claim-late-not-typable : ¬ Typable [] (claim-after (# 1) (1 / 2) (3 / 4))
claim-late-not-typable =
  infer-untypable [] (claim-after (# 1) (1 / 2) (3 / 4)) claim-late-verdict

------------------------------------------------------------------
-- 2. Inferred grade: a lease of at least three quarters

inferred-grade-reported :
  schemeOf (infer [] (inferred-grade (1 / 2) (1 / 4)))
  ≡ just (expected-inferred-grade (3 / 4))
inferred-grade-reported = refl
