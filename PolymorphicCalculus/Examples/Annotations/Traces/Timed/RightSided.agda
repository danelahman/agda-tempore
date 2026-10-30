------------------------------------------------------------------
-- Annotated programs at timed traces, allowance order          --
--                                                              --
-- Every scheme is the one written in `Annotations`.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-RightSided)

module PolymorphicCalculus.Examples.Annotations.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Examples.Annotations spec hints enum

id-bool-reported : schemeOf (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : schemeOf (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : schemeOf (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl
