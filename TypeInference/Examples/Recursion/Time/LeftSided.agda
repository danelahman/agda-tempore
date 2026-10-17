------------------------------------------------------------------
-- Primitive recursion at left-sided intervals                  --
--                                                              --
-- "At least `n` ticks": the unit is the top, so `ε · ε ≾ ε`    --
-- always holds, and the base's `u ≾ ε` makes every recursion's --
-- effect the unit. A countdown on three is refuted at three    --
-- ticks, although each of its runs takes three. A function is  --
-- usable in the step, `⊤ᵣ ≾ uᵣ` holding. Recursion inside an   --
-- operation clause is typed, but a clause dropping its         --
-- continuation after a countdown is refuted.                   --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Syntax.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-LeftSided)

module TypeInference.Examples.Recursion.Time.LeftSided where

open Time-LeftSided using (spec; enum)

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Recursion spec enum ℕᴰ-stepped

------------------------------------------------------------------
-- 1. Pure recursion

expected-add : Scheme
expected-add = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

add-reported : schemeOf (infer [] add) ≡ just expected-add
add-reported = refl

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step

expected-rebuild : Scheme
expected-rebuild = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ

rebuild-reported : schemeOf (infer [] rebuild) ≡ just expected-rebuild
rebuild-reported = refl

mul-reported : schemeOf (infer [] mul) ≡ just expected-add
mul-reported = refl

------------------------------------------------------------------
-- 3. A function from outside the step: usable

expected-each : Scheme
expected-each =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ ((Unit ⇒ Unit ‼ ûₑ) ⇒ (Nat ⇒ Unit ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

each-reported : schemeOf (infer [] each) ≡ just expected-each
each-reported = refl

------------------------------------------------------------------
-- 4. A countdown: the effect is the unit

expected-countdown : Scheme
expected-countdown = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Unit ‼ ûₑ) ‼ ûₑ

countdown-reported : schemeOf (infer [] countdown) ≡ just expected-countdown
countdown-reported = refl

countdown-at-0-reported :
  schemeOf (infer [] (countdown-at 0)) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ûₑ)
countdown-at-0-reported = refl

-- annotated at three ticks: refuted, the base forcing the unit

countdown-at-3-verdict : infer [] (countdown-at 3) ≡ untypable
countdown-at-3-verdict = refl

countdown-at-3-not-typable : ¬ Typable [] (countdown-at 3)
countdown-at-3-not-typable = infer-untypable [] (countdown-at 3) countdown-at-3-verdict

------------------------------------------------------------------
-- 5. Recursion inside an operation clause: typed and established

in-clause-pure-reported :
  schemeOf (infer [] in-clause-pure) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ûₑ)
in-clause-pure-reported = refl

in-clause-tick-reported :
  schemeOf (infer [] in-clause-tick) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ûₑ)
in-clause-tick-reported = refl

in-clause-tick-verdict : verdict (check [] in-clause-tick) ≡ established
in-clause-tick-verdict = refl

------------------------------------------------------------------
-- 6. A clause dropping its continuation: refuted

drop-clause-verdict : infer [] drop-clause ≡ untypable
drop-clause-verdict = refl

drop-clause-check : verdict (check [] drop-clause) ≡ untypable
drop-clause-check = refl

drop-clause-not-typable : ¬ Typable [] drop-clause
drop-clause-not-typable = infer-untypable [] drop-clause drop-clause-verdict
