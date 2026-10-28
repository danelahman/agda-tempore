-------------------------------------------------------------------
-- Handlers at timed traces, coverage order                      --
--                                                               --
-- Every scheme is the one written in `Handlers`.                --
-- `resume-twice` is typed, the unit being the top; `discard` is --
-- refuted.                                                      --
-------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Traces-Timed-LeftSided)

module OpenCalculus.Examples.Handlers.Traces.Timed.LeftSided where

open Traces-Timed-LeftSided using (spec; enum)

open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Inference.Principality spec using (Typable; untypable)
open import OpenCalculus.Inference.SolverImpl spec enum using (infer-untypable)
open import OpenCalculus.Examples.Handlers spec enum

relay-reported : schemeOf (infer [] relay) ≡ just expected-relay
relay-reported = refl

relay-boxed-reported : schemeOf (infer [] relay-boxed) ≡ just expected-relay-boxed
relay-boxed-reported = refl

-- The unit is the top, so the continuation may be spent twice and
-- nothing goes stale

resume-twice-reported : schemeOf (infer [] resume-twice) ≡ just expected-resume-twice
resume-twice-reported = refl

resume-twice-derivable : Typable [] resume-twice
resume-twice-derivable = resume-twice-typable _

-- Returning at once is not below `op-grade read`: `no-discarding` in
-- `ClosedCalculus/Examples/Typing/Traces/Timed/LeftSided.agda`

discard-untypable-verdict : infer [] discard ≡ untypable
discard-untypable-verdict = refl

discard-not-typable : ¬ Typable [] discard
discard-not-typable = infer-untypable [] discard discard-untypable-verdict