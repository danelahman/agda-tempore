------------------------------------------------------------------
-- Primitive recursion at right-sided intervals                 --
--                                                              --
-- "At most `n` ticks": `ε · ε ≾ ε` holds only at the unit and  --
-- at the top, so a recursion's effect is one of the two: the   --
-- closure of its lower bounds. The pure programs have the      --
-- unit; a countdown, a tick a step, has the top, so one        --
-- annotated at a finite bound is refuted, and so is one inside --
-- an operation clause. A function is not usable in the step. A --
-- pure recursion inside an operation clause is typed. A clause --
-- dropping its continuation after a countdown is refuted by    --
-- the report's closed check.                                   --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Syntax.Durations.Nat using (ℕᴰ-stepped)
open import Syntax.Grades using (module GradeSystemInterface)
open import Syntax.LanguageSpec using (LanguageSpec)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-RightSided)

module TypeInference.Examples.Recursion.Time.RightSided where

open Time-RightSided using (spec; enum)
open GradeSystemInterface (LanguageSpec.Grades spec) using (⊤ₑ)

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Recursion spec enum ℕᴰ-stepped
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- 1. Pure recursion: the effect is lowered to the unit, at which
-- its cycle holds

expected-add : Scheme
expected-add = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

add-reported : schemeOf (infer [] add) ≡ just expected-add
add-reported = refl

add-verdict : verdict (check [] add) ≡ established
add-verdict = refl

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step

expected-rebuild : Scheme
expected-rebuild = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ

rebuild-reported : schemeOf (infer [] rebuild) ≡ just expected-rebuild
rebuild-reported = refl

-- both recursions' effects the unit

mul-reported : schemeOf (infer [] mul) ≡ just expected-add
mul-reported = refl

mul-verdict : verdict (check [] mul) ≡ established
mul-verdict = refl

------------------------------------------------------------------
-- 3. A function from outside the step: `⊤ᵣ ≾ uᵣ` fails

each-verdict : infer [] each ≡ untypable
each-verdict = refl

each-not-typable : ¬ Typable [] each
each-not-typable = infer-untypable [] each each-verdict

------------------------------------------------------------------
-- 4. A countdown: at least a tick, absorbing itself, so the top,
-- the closure of a tick

expected-countdown : Scheme
expected-countdown = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (Nat ⇒ Unit ‼ econst ⊤ₑ) ‼ ûₑ

countdown-reported : schemeOf (infer [] countdown) ≡ just expected-countdown
countdown-reported = refl

countdown-verdict : verdict (check [] countdown) ≡ established
countdown-verdict = refl

countdown-typable : Typable [] countdown
countdown-typable = check-typable [] countdown countdown-verdict

-- annotated at the top: established, and typable by `countdown-top-D`

countdown-top-verdict : verdict (check [] countdown-top) ≡ established
countdown-top-verdict = refl

-- annotated at no tick: refuted

countdown-at-0-verdict : infer [] (countdown-at 0) ≡ untypable
countdown-at-0-verdict = refl

countdown-at-0-not-typable : ¬ Typable [] (countdown-at 0)
countdown-at-0-not-typable = infer-untypable [] (countdown-at 0) countdown-at-0-verdict

-- annotated at three ticks: the effect is lowered to the top, and
-- `⊤ ≾ ⌜ 3 ⌝` is closed and false

countdown-at-3-verdict : infer [] (countdown-at 3) ≡ untypable
countdown-at-3-verdict = refl

countdown-at-3-not-typable : ¬ Typable [] (countdown-at 3)
countdown-at-3-not-typable = infer-untypable [] (countdown-at 3) countdown-at-3-verdict

-- two ticks annotated at one: refuted the same way

wait-2-at-1-verdict : infer [] wait-2-at-1 ≡ untypable
wait-2-at-1-verdict = refl

wait-2-at-1-not-typable : ¬ Typable [] wait-2-at-1
wait-2-at-1-not-typable = infer-untypable [] wait-2-at-1 wait-2-at-1-verdict

------------------------------------------------------------------
-- 5. Recursion inside an operation clause: with a pure step, the
-- recursion's effect is lowered to the unit in the clause, as in
-- `in-clause-pure-D`; with a tick a step, to the top, which no
-- finite bound of the clause admits

in-clause-pure-reported :
  schemeOf (infer [] in-clause-pure) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ Unit ‼ ûₑ)
in-clause-pure-reported = refl

in-clause-pure-check : verdict (check [] in-clause-pure) ≡ established
in-clause-pure-check = refl

in-clause-tick-verdict : infer [] in-clause-tick ≡ untypable
in-clause-tick-verdict = refl

in-clause-tick-not-typable : ¬ Typable [] in-clause-tick
in-clause-tick-not-typable = infer-untypable [] in-clause-tick in-clause-tick-verdict

------------------------------------------------------------------
-- 6. A clause dropping its continuation: in the clause for `read`
-- the effect is equated with `⌜ 1 ⌝`, and the report keeps
-- `⌜ 1 ⌝ · ⌜ 1 ⌝ ≾ ⌜ 1 ⌝`, closed and false

drop-clause-verdict : infer [] drop-clause ≡ untypable
drop-clause-verdict = refl

drop-clause-check : verdict (check [] drop-clause) ≡ untypable
drop-clause-check = refl

drop-clause-not-typable : ¬ Typable [] drop-clause
drop-clause-not-typable = infer-untypable [] drop-clause drop-clause-verdict
