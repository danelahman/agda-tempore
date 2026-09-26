------------------------------------------------------------------
-- Annotated programs at timed traces, allowance order          --
--                                                              --
-- Every scheme is the one written in `Annotations`.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Traces-Timed-RightSided)

module TypeInference.Examples.Annotations.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Annotations spec enum

id-bool-reported : scheme (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : scheme (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : scheme (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl
