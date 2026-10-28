------------------------------------------------------------------
-- Annotated programs at left-sided intervals                   --
--                                                              --
-- Every scheme is the one written in `Annotations`.            --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Time-LeftSided)

module OpenCalculus.Examples.Annotations.Time.LeftSided where

open Time-LeftSided using (spec; enum)

open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Examples.Annotations spec enum

id-bool-reported : schemeOf (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : schemeOf (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : schemeOf (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl
