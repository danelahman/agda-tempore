------------------------------------------------------------------------
-- Natural numbers, sums and lists at right-sided intervals           --
--                                                                    --
-- After a delay only variables of eternal type are usable: a         --
-- variable of unknown type is asked to be eternal, and a function,   --
-- alone or in a sum or a list, is refuted. A join of delays is the   --
-- longer. The eliminations at the wrong type are refuted.            --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)

module PolymorphicCalculus.Examples.Data.Time.RightSided where

open Time-RightSided using (spec; hints; enum)

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
-- 2. Under a modality: a `nat` survives a tick, a function does not,
-- and an unknown type is asked to be eternal

later-succ-reported : schemeOf (infer [] later-succ) ≡ just expected-later-succ
later-succ-reported = refl

later-id-reported : schemeOf (infer [] later-id) ≡ just expected-later-id-eternal
later-id-reported = refl

numeral-later-reported : schemeOf (infer [] numeral-later) ≡ just expected-numeral-later
numeral-later-reported = refl

function-later-verdict : infer [] function-later ≡ untypable
function-later-verdict = refl

function-later-not-typable : ¬ Typable [] function-later
function-later-not-typable = infer-untypable [] function-later function-later-verdict

------------------------------------------------------------------
-- 3. A boxed numeral, claimed on time

boxed-numeral-reported : schemeOf (infer [] boxed-numeral) ≡ just expected-boxed-numeral
boxed-numeral-reported = refl

------------------------------------------------------------------
-- 4. Branches of different effects: the join is three ticks

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

inl-later-reported : schemeOf (infer [] inl-later) ≡ just expected-inl-later-eternal
inl-later-reported = refl

fun-sum-later-verdict : infer [] fun-sum-later ≡ untypable
fun-sum-later-verdict = refl

fun-sum-later-not-typable : ¬ Typable [] fun-sum-later
fun-sum-later-not-typable = infer-untypable [] fun-sum-later fun-sum-later-verdict

------------------------------------------------------------------
-- 6. Lists

head-or-reported : schemeOf (infer [] head-or) ≡ just expected-head-or
head-or-reported = refl

list-later-reported : schemeOf (infer [] list-later) ≡ just expected-list-later
list-later-reported = refl

nil-later-reported : schemeOf (infer [] nil-later) ≡ just expected-nil-later-eternal
nil-later-reported = refl

fun-list-later-verdict : infer [] fun-list-later ≡ untypable
fun-list-later-verdict = refl

fun-list-later-not-typable : ¬ Typable [] fun-list-later
fun-list-later-not-typable = infer-untypable [] fun-list-later fun-list-later-verdict

match-on-nat-verdict : infer [] match-on-nat ≡ untypable
match-on-nat-verdict = refl

match-on-nat-not-typable : ¬ Typable [] match-on-nat
match-on-nat-not-typable = infer-untypable [] match-on-nat match-on-nat-verdict
