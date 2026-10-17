------------------------------------------------------------------
-- Primitive recursion at right-sided intervals                 --
--                                                              --
-- "At most `n` ticks": `ε · ε ≾ ε` holds only at the unit and  --
-- at the top, so a recursion's effect is one of the two. The   --
-- pure programs keep it as a qualified variable, which the     --
-- check establishes; a countdown, a tick a step, needs the     --
-- top. A function is not usable in the step. Recursion inside  --
-- an operation clause is stuck: `Localise` gives the cycle     --
-- `ε · ε ≾ ε` no value. A clause dropping its continuation     --
-- after a countdown is refuted by the report's closed check.   --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Syntax.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import TypeInference.Examples.Specs using (module Time-RightSided)

module TypeInference.Examples.Recursion.Time.RightSided where

open Time-RightSided using (spec; enum)

open import TypeInference.OpenSyntax.Grades   spec
open import TypeInference.OpenSyntax.Types    spec
open import TypeInference.OpenSyntax.Contexts spec using ([])
open import TypeInference.Principality spec using (Typable; untypable; stuck)
open import TypeInference.SolverImpl spec enum using (infer-untypable)
open import TypeInference.Examples.Recursion spec enum ℕᴰ-stepped
open import TypeInference.Examples.Variables

------------------------------------------------------------------
-- 1. Pure recursion: the effect a qualified variable

expected-add : Scheme
expected-add =
  ∀[ 0 , 0 , 1 ] (ε₀ ·̂ₑ ε₀ ≾ₑ ε₀) ⟹ (Nat ⇒ (Nat ⇒ Nat ‼ ε₀) ‼ ûₑ) ‼ ûₑ

add-reported : schemeOf (infer [] add) ≡ just expected-add
add-reported = refl

add-verdict : verdict (check [] add) ≡ established
add-verdict = refl

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step

expected-rebuild : Scheme
expected-rebuild =
  ∀[ 0 , 0 , 1 ] (ε₀ ·̂ₑ ε₀ ≾ₑ ε₀) ⟹ (Nat ⇒ Nat ‼ ε₀) ‼ ûₑ

rebuild-reported : schemeOf (infer [] rebuild) ≡ just expected-rebuild
rebuild-reported = refl

-- the inner recursion's effect is below the outer one's

expected-mul : Scheme
expected-mul =
  ∀[ 0 , 0 , 2 ] (ε₀ ≾ₑ ε₁) ∧ (ε₀ ·̂ₑ ε₀ ≾ₑ ε₀) ∧ (ε₁ ·̂ₑ ε₁ ≾ₑ ε₁)
    ⟹ (Nat ⇒ (Nat ⇒ Nat ‼ ε₁) ‼ ûₑ) ‼ ûₑ

mul-reported : schemeOf (infer [] mul) ≡ just expected-mul
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
-- 4. A countdown: at least a tick, absorbing itself, so the top

expected-countdown : Scheme
expected-countdown =
  ∀[ 0 , 0 , 1 ] (⌜ 1 ⌝ᵉ ≾ₑ ε₀) ∧ (ε₀ ·̂ₑ ε₀ ≾ₑ ε₀) ⟹ (Nat ⇒ Unit ‼ ε₀) ‼ ûₑ

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

-- annotated at three ticks: `ε₀ ≾ ⌜ 3 ⌝` with `⌜ 1 ⌝ ≾ ε₀` has no
-- chain to a refutation, and no candidate is a closed instance, so
-- nothing is claimed

expected-countdown-at-3 : Scheme
expected-countdown-at-3 =
  ∀[ 0 , 0 , 1 ] (⌜ 1 ⌝ᵉ ≾ₑ ε₀) ∧ (ε₀ ≾ₑ ⌜ 3 ⌝ᵉ) ∧ (ε₀ ·̂ₑ ε₀ ≾ₑ ε₀) ⟹ Unit ‼ ⌜ 3 ⌝ᵉ

countdown-at-3-reported : schemeOf (infer [] (countdown-at 3)) ≡ just expected-countdown-at-3
countdown-at-3-reported = refl

countdown-at-3-verdict : verdict (check [] (countdown-at 3)) ≡ unestablished
countdown-at-3-verdict = refl

------------------------------------------------------------------
-- 5. Recursion inside an operation clause: stuck, with a pure step
-- although typable (`in-clause-pure-D`), and with a tick

in-clause-pure-verdict : infer [] in-clause-pure ≡ stuck
in-clause-pure-verdict = refl

in-clause-pure-check : verdict (check [] in-clause-pure) ≡ stuck
in-clause-pure-check = refl

in-clause-tick-verdict : infer [] in-clause-tick ≡ stuck
in-clause-tick-verdict = refl

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
