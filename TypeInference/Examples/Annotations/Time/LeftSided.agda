------------------------------------------------------------------
-- Annotated programs at left-sided intervals                    --
--                                                                --
-- Every scheme is the one written in `Annotations`. Inference   --
-- is stuck on `relay`, and types `relayᵃ`.                     --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-LeftSided)

module TypeInference.Examples.Annotations.Time.LeftSided where

open Time-LeftSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality        spec using (stuck)
open import TypeInference.Examples.Annotations spec enum

id-bool-reported : report (infer [] id-bool) ≡ just expected-id-bool
id-bool-reported = refl

id-unit-reported : report (infer [] id-unit) ≡ just expected-id-unit
id-unit-reported = refl

compose-g-reported : report (infer [] compose-g) ≡ just expected-compose-g
compose-g-reported = refl

relay-stuck : infer [] relay ≡ stuck
relay-stuck = refl

relayᵃ-reported : report (infer [] relayᵃ) ≡ just expected-relayᵃ
relayᵃ-reported = refl
