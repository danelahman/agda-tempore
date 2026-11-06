------------------------------------------------------------------------
-- Handlers at banked trace upper bounds, allowance order             --
--                                                                    --
-- The unit is least. Every program gets the scheme written in        --
-- `Handlers`; `discard` is typable, and `resume-twice` is refuted.   --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import Grades.Examples.Worked.Traces.Banked.UpperBound using (≾-⊥)
open import PolymorphicCalculus.Examples.Specs using (module Traces-Banked-UpperBound)

module PolymorphicCalculus.Examples.Handlers.Traces.Banked.UpperBound where

open Traces-Banked-UpperBound using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Handlers spec hints enum

relay-reported : schemeOf (infer [] relay) ≡ just expected-relay
relay-reported = refl

relay-boxed-reported : schemeOf (infer [] relay-boxed) ≡ just expected-relay-boxed
relay-boxed-reported = refl

-- Handlers as values

bound-reported : schemeOf (infer [] bound) ≡ just expected-bound
bound-reported = refl

run-reported : schemeOf (infer [] run) ≡ just expected-run
run-reported = refl

run-forward-reported : schemeOf (infer [] run-forward) ≡ just expected-run-forward
run-forward-reported = refl

-- The unit is least, so the clause may drop its continuation

discard-reported : schemeOf (infer [] discard) ≡ just expected-discard
discard-reported = refl

discard-derivable : Typable [] discard
discard-derivable = discard-typable ≾-⊥

-- `j` above the unit is spent twice, and `k'` and `a` go stale

resume-twice-untypable-verdict : infer [] resume-twice ≡ untypable
resume-twice-untypable-verdict = refl

resume-twice-not-typable : ¬ Typable [] resume-twice
resume-twice-not-typable =
  infer-untypable [] resume-twice resume-twice-untypable-verdict
