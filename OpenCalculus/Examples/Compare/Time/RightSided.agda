------------------------------------------------------------------
-- Comparisons at right-sided intervals                         --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import OpenCalculus.Examples.Specs using (module Time-RightSided)

module OpenCalculus.Examples.Compare.Time.RightSided where

open Time-RightSided using (spec; enum)

open import OpenCalculus.Syntax.Contexts spec using ([])
open import OpenCalculus.Inference.Principality spec using (Typable; untypable)
open import OpenCalculus.Inference.SolverImpl spec enum using (infer-untypable)
open import OpenCalculus.Examples.Compare spec enum ℕᴰ-stepped

------------------------------------------------------------------
-- 1.–3. Natural numbers, lists, pairs and sums

lt-nats-reported : schemeOf (infer [] lt-nats) ≡ just expected-lt-nats
lt-nats-reported = refl

eq-lists-reported : schemeOf (infer [] eq-lists) ≡ just expected-eq-lists
eq-lists-reported = refl

ge-pairs-reported : schemeOf (infer [] ge-pairs) ≡ just expected-ge-pairs
ge-pairs-reported = refl

ne-sums-reported : schemeOf (infer [] ne-sums) ≡ just expected-ne-sums
ne-sums-reported = refl

ne-sums'-reported : schemeOf (infer [] ne-sums') ≡ just expected-ne-sums'
ne-sums'-reported = refl

------------------------------------------------------------------
-- 4. A polymorphic comparison

equal-reported : schemeOf (infer [] equal) ≡ just expected-equal
equal-reported = refl

reflexive-reported : schemeOf (infer [] reflexive) ≡ just expected-reflexive
reflexive-reported = refl

------------------------------------------------------------------
-- 5. Functions and boxes do not compare

eq-funs-verdict : infer [] eq-funs ≡ untypable
eq-funs-verdict = refl

eq-funs-not-typable : ¬ Typable [] eq-funs
eq-funs-not-typable = infer-untypable [] eq-funs eq-funs-verdict

eq-boxes-verdict : infer [] eq-boxes ≡ untypable
eq-boxes-verdict = refl

eq-boxes-not-typable : ¬ Typable [] eq-boxes
eq-boxes-not-typable = infer-untypable [] eq-boxes eq-boxes-verdict

------------------------------------------------------------------
-- 6. Comparisons under a lock

later-lt-reported : schemeOf (infer [] later-lt) ≡ just expected-later-lt
later-lt-reported = refl

later-equal-reported : schemeOf (infer [] later-equal) ≡ just expected-later-equal
later-equal-reported = refl
