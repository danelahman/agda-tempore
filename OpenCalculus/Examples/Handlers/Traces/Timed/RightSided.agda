------------------------------------------------------------------
-- Handlers at timed traces, allowance order                    --
--                                                              --
-- Every scheme is the one written in `Handlers`.               --
-- `discard` is typed, the unit being least; `resume-twice` is  --
-- refuted.                                                     --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to is-just)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Traces-Timed-RightSided)

module OpenCalculus.Examples.Handlers.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; enum)

open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Inference.Principality spec using (Typable; untypable)
open import OpenCalculus.Inference.SolverImpl spec enum using (infer-untypable)
open import OpenCalculus.Examples.Handlers spec enum

relay-reported : schemeOf (infer [] relay) ≡ just expected-relay
relay-reported = refl

relay-boxed-reported : schemeOf (infer [] relay-boxed) ≡ just expected-relay-boxed
relay-boxed-reported = refl

-- A handler as a value: bound by `let`, taken as an argument, and
-- passed to a function

bound-reported : schemeOf (infer [] bound) ≡ just expected-bound
bound-reported = refl

run-reported : schemeOf (infer [] run) ≡ just expected-run
run-reported = refl

run-forward-reported : schemeOf (infer [] run-forward) ≡ just expected-run-forward
run-forward-reported = refl

-- The unit is least, so the clause may drop its continuation

discard-reported : schemeOf (infer [] discard) ≡ just expected-discard
discard-reported = refl

discard-derivable : Typable [] discard
discard-derivable = discard-typable (is-just tt)

-- A continuation grade above the unit is spent twice, and `k'` and
-- `a` go stale across it

resume-twice-untypable-verdict : infer [] resume-twice ≡ untypable
resume-twice-untypable-verdict = refl

resume-twice-not-typable : ¬ Typable [] resume-twice
resume-twice-not-typable =
  infer-untypable [] resume-twice resume-twice-untypable-verdict
