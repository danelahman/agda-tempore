------------------------------------------------------------------
-- Annotated programs at timed traces, coverage order            --
--                                                                --
-- Every scheme is the one written in `Annotations`.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Traces-Timed-LeftSided)

module TypeInference.Examples.Annotations.Traces.Timed.LeftSided where

open Traces-Timed-LeftSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Annotations spec enum

id-bool-reported : report (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : report (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : report (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl
