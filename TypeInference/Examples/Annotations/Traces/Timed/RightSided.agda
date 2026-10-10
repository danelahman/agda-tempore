------------------------------------------------------------------
-- Annotated programs at timed traces, allowance order          --
--                                                              --
-- Every scheme is the one written in `Annotations`.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)
open import Relation.Nullary using (¬_)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Traces-Timed-RightSided)

module TypeInference.Examples.Annotations.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Annotations spec enum

id-bool-reported : schemeOf (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : schemeOf (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : schemeOf (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl

unbox-bool-reported : schemeOf (infer [] unbox-bool) ≡ just expected-unbox-bool
unbox-bool-reported = refl

unbox-reject-verdict : infer [] unbox-reject ≡ untypable
unbox-reject-verdict = refl

unbox-reject-not-typable : ¬ Typable [] unbox-reject
unbox-reject-not-typable = infer-untypable [] unbox-reject unbox-reject-verdict
