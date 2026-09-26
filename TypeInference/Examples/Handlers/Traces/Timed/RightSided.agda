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

open import TypeInference.Examples.Specs using (module Traces-Timed-RightSided)

module TypeInference.Examples.Handlers.Traces.Timed.RightSided where

open Traces-Timed-RightSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Handlers spec enum

relay-reported : scheme (infer [] relay) ≡ just expected-relay
relay-reported = refl

relay-boxed-reported : scheme (infer [] relay-boxed) ≡ just expected-relay-boxed
relay-boxed-reported = refl

-- The unit is least, so the clause may drop its continuation

discard-reported : scheme (infer [] discard) ≡ just expected-discard
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
