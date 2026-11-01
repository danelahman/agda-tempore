------------------------------------------------------------------------
-- Annotated programs at timed traces, coverage order                 --
--                                                                    --
-- Every program gets the scheme written in `Annotations`.            --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Traces-Timed-LeftSided)

module PolymorphicCalculus.Examples.Annotations.Traces.Timed.LeftSided where

open Traces-Timed-LeftSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Examples.Annotations spec hints enum

id-bool-reported : schemeOf (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : schemeOf (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : schemeOf (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl
