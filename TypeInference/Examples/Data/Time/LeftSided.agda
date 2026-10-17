------------------------------------------------------------------
-- Natural numbers at left-sided intervals                      --
--                                                              --
-- "At least `n` ticks": `var`'s bound `ρ ≾ uᵣ` holds at every  --
-- grade, so nothing goes stale and eternality is never asked   --
-- for. A join of delays is the shorter.                        --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Syntax.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-LeftSided)

module TypeInference.Examples.Data.Time.LeftSided where

open Time-LeftSided using (spec; enum)

open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Data spec enum ℕᴰ-stepped

------------------------------------------------------------------
-- 1. Eliminating a natural number

is-zero-reported : schemeOf (infer [] is-zero) ≡ just expected-is-zero
is-zero-reported = refl

pred-reported : schemeOf (infer [] pred) ≡ just expected-pred
pred-reported = refl

case-of-bool-verdict : infer [] case-of-bool ≡ untypable
case-of-bool-verdict = refl

case-of-bool-not-typable : ¬ Typable [] case-of-bool
case-of-bool-not-typable = infer-untypable [] case-of-bool case-of-bool-verdict

------------------------------------------------------------------
-- 2. Under a lock: a `Nat`, an unknown type and a function all
-- survive a tick

later-succ-reported : schemeOf (infer [] later-succ) ≡ just expected-later-succ
later-succ-reported = refl

later-id-reported : schemeOf (infer [] later-id) ≡ just expected-later-id
later-id-reported = refl

numeral-later-reported : schemeOf (infer [] numeral-later) ≡ just expected-numeral-later
numeral-later-reported = refl

function-later-reported : schemeOf (infer [] function-later) ≡ just expected-function-later
function-later-reported = refl

function-later-derivable : Typable [] function-later
function-later-derivable = function-later-typable _

------------------------------------------------------------------
-- 3. A boxed numeral, claimed on time

boxed-numeral-reported : schemeOf (infer [] boxed-numeral) ≡ just expected-boxed-numeral
boxed-numeral-reported = refl

------------------------------------------------------------------
-- 4. Branches of different effects: the join is one tick

joined-reported : schemeOf (infer [] joined) ≡ just expected-joined
joined-reported = refl
