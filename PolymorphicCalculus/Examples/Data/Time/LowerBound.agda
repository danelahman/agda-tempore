------------------------------------------------------------------------
-- Natural numbers, sums and lists at lower bounds                    --
--                                                                    --
-- Nothing goes stale and eternality is never asked for: every        --
-- example using a value after a delay is typed, functions included.  --
-- A join of delays is the shorter. The eliminations at the wrong     --
-- type are refuted.                                                  --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-LowerBound)

module PolymorphicCalculus.Examples.Data.Time.LowerBound where

open Time-LowerBound using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Data spec hints enum ℕᴰ-stepped

------------------------------------------------------------------
-- 1. Eliminating a natural number

is-zero-reported : schemeOf (infer [] is-zero) ≡ just expected-is-zero
is-zero-reported = refl

pred-reported : schemeOf (infer [] pred) ≡ just expected-pred
pred-reported = refl

match-on-bool-verdict : infer [] match-on-bool ≡ untypable
match-on-bool-verdict = refl

match-on-bool-not-typable : ¬ Typable [] match-on-bool
match-on-bool-not-typable = infer-untypable [] match-on-bool match-on-bool-verdict

------------------------------------------------------------------
-- 2. Under a modality: a `nat`, an unknown type and a function all
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

------------------------------------------------------------------
-- 5. Sums

swap-reported : schemeOf (infer [] swap) ≡ just expected-swap
swap-reported = refl

choose-reported : schemeOf (infer [] choose) ≡ just expected-choose
choose-reported = refl

subsume-sum-reported : schemeOf (infer [] subsume-sum) ≡ just expected-subsume-sum
subsume-sum-reported = refl

sum-later-reported : schemeOf (infer [] sum-later) ≡ just expected-sum-later
sum-later-reported = refl

match-on-bool+-verdict : infer [] match-on-bool+ ≡ untypable
match-on-bool+-verdict = refl

match-on-bool+-not-typable : ¬ Typable [] match-on-bool+
match-on-bool+-not-typable = infer-untypable [] match-on-bool+ match-on-bool+-verdict

inl-later-reported : schemeOf (infer [] inl-later) ≡ just expected-inl-later
inl-later-reported = refl

fun-sum-later-reported : schemeOf (infer [] fun-sum-later) ≡ just expected-fun-sum-later
fun-sum-later-reported = refl

fun-sum-later-derivable : Typable [] fun-sum-later
fun-sum-later-derivable = fun-sum-later-typable _

------------------------------------------------------------------
-- 6. Lists

head-or-reported : schemeOf (infer [] head-or) ≡ just expected-head-or
head-or-reported = refl

list-later-reported : schemeOf (infer [] list-later) ≡ just expected-list-later
list-later-reported = refl

nil-later-reported : schemeOf (infer [] nil-later) ≡ just expected-nil-later
nil-later-reported = refl

fun-list-later-reported : schemeOf (infer [] fun-list-later) ≡ just expected-fun-list-later
fun-list-later-reported = refl

fun-list-later-derivable : Typable [] fun-list-later
fun-list-later-derivable = fun-list-later-typable _

match-on-nat-verdict : infer [] match-on-nat ≡ untypable
match-on-nat-verdict = refl

match-on-nat-not-typable : ¬ Typable [] match-on-nat
match-on-nat-not-typable = infer-untypable [] match-on-nat match-on-nat-verdict
