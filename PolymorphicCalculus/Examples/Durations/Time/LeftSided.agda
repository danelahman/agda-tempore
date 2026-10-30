------------------------------------------------------------------
-- Durations at left-sided intervals of dense time              --
--                                                              --
-- A box is a promise: two half-unit delays meet a promise of   --
-- one unit; a half and a quarter fall short.                   --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Util.NonNegativeRational
  using (_/_; #_; nonZero)

open import PolymorphicCalculus.Examples.Specs using (module Dense-Time-LeftSided)

module PolymorphicCalculus.Examples.Durations.Time.LeftSided where

open Dense-Time-LeftSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Durations spec hints enum

------------------------------------------------------------------
-- 1. A promise of one unit: claimed after two half units and
-- after a half and three quarters, not after a half and a quarter

claim-on-time-reported :
  schemeOf (infer [] (claim-after (# 1) (1 / 2) (1 / 2)))
  ≡ just (expected-claim-after (# 1))
claim-on-time-reported = refl

claim-on-time-derivable : Typable [] (claim-after (# 1) (1 / 2) (1 / 2))
claim-on-time-derivable = claim-after-typable (# 1) (1 / 2) (1 / 2) _

claim-late-reported :
  schemeOf (infer [] (claim-after (# 1) (1 / 2) (3 / 4)))
  ≡ just (expected-claim-after (5 / 4))
claim-late-reported = refl

-- the early claim fails its premise `[ 3 / 4 ,+∞⟩ ≾ [ 1 ,+∞⟩`

claim-early-verdict : infer [] (claim-after (# 1) (1 / 2) (1 / 4)) ≡ untypable
claim-early-verdict = refl

claim-early-not-typable : ¬ Typable [] (claim-after (# 1) (1 / 2) (1 / 4))
claim-early-not-typable =
  infer-untypable [] (claim-after (# 1) (1 / 2) (1 / 4)) claim-early-verdict

------------------------------------------------------------------
-- 2. Inferred grade: a promise due within three quarters

inferred-grade-reported :
  schemeOf (infer [] (inferred-grade (1 / 2) (1 / 4)))
  ≡ just (expected-inferred-grade (3 / 4))
inferred-grade-reported = refl
