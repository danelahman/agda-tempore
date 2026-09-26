------------------------------------------------------------------
-- The standard library at timed traces, allowance order          --
--                                                                --
-- The unit is least, and multiplication does not commute: every  --
-- scheme is the shared one.                                      --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Traces-Timed-RightSided)

module TypeInference.Examples.Stdlib.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; enum)

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Examples.Stdlib     spec enum
open import TypeInference.Examples.Variables

id-reported : scheme (infer [] id) ≡ just expected-id
id-reported = refl

ignore-reported : scheme (infer [] ignore) ≡ just expected-ignore
ignore-reported = refl

fst-reported : scheme (infer [] fst) ≡ just expected-fst
fst-reported = refl

snd-reported : scheme (infer [] snd) ≡ just expected-snd
snd-reported = refl

not-reported : scheme (infer [] not) ≡ just expected-not
not-reported = refl

absurd′-reported : scheme (infer [] absurd′) ≡ just expected-absurd′
absurd′-reported = refl

pipe-reported : scheme (infer [] pipe) ≡ just expected-pipe
pipe-reported = refl

compose-reported : scheme (infer [] compose) ≡ just expected-compose
compose-reported = refl

min-reported : scheme (infer [] min) ≡ just expected-min
min-reported = refl
