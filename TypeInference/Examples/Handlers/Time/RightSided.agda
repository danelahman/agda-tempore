------------------------------------------------------------------
-- Handlers at right-sided intervals                              --
--                                                                --
-- Every scheme is the one written in `Handlers`.                 --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-RightSided)

module TypeInference.Examples.Handlers.Time.RightSided where

open Time-RightSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Handlers spec enum

relay-reported : report (infer [] relay) ≡ just expected-relay
relay-reported = refl

abort-reported : report (infer [] abort) ≡ just expected-abort
abort-reported = refl
