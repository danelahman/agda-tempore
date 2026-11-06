------------------------------------------------------------------------
-- Handlers at banked trace lower bounds, coverage order              --
--                                                                    --
-- The unit is the greatest grade. Every program gets the scheme      --
-- written in `Handlers`; `resume-twice` is typable, and `discard` is --
-- refuted.                                                           --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Traces-Banked-LowerBound)

module PolymorphicCalculus.Examples.Handlers.Traces.Banked.LowerBound where

open Traces-Banked-LowerBound using (spec; hints; enum)

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

-- The unit is the top: spending `j` twice costs nothing

resume-twice-reported : schemeOf (infer [] resume-twice) ≡ just expected-resume-twice
resume-twice-reported = refl

resume-twice-derivable : Typable [] resume-twice
resume-twice-derivable = resume-twice-typable _

-- Returning at once is not below `op-grade read`

discard-untypable-verdict : infer [] discard ≡ untypable
discard-untypable-verdict = refl

discard-not-typable : ¬ Typable [] discard
discard-not-typable = infer-untypable [] discard discard-untypable-verdict