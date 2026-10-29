-------------------------------------------------------------------
-- The standard library at timed traces, allowance order         --
--                                                               --
-- The unit is least, and multiplication does not commute: every --
-- scheme is the shared one.                                     --
-------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Traces-Timed-RightSided)

module OpenCalculus.Examples.Stdlib.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; hints; enum)

open import OpenCalculus.Syntax.Grades   spec
open import OpenCalculus.Syntax.Types    spec
open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Examples.Stdlib spec hints enum
open import OpenCalculus.Examples.Variables

id-reported : schemeOf (infer [] id) ≡ just expected-id
id-reported = refl

ignore-reported : schemeOf (infer [] ignore) ≡ just expected-ignore
ignore-reported = refl

fst-reported : schemeOf (infer [] fst) ≡ just expected-fst
fst-reported = refl

snd-reported : schemeOf (infer [] snd) ≡ just expected-snd
snd-reported = refl

not-reported : schemeOf (infer [] not) ≡ just expected-not
not-reported = refl

absurd′-reported : schemeOf (infer [] absurd′) ≡ just expected-absurd′
absurd′-reported = refl

pipe-reported : schemeOf (infer [] pipe) ≡ just expected-pipe
pipe-reported = refl

compose-reported : schemeOf (infer [] compose) ≡ just expected-compose
compose-reported = refl

min-reported : schemeOf (infer [] min) ≡ just expected-min
min-reported = refl
