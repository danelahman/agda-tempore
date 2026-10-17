------------------------------------------------------------------
-- Primitive recursion at left-sided intervals                  --
--                                                              --
-- "At least `n` ticks": the unit is the top, so `ε · ε ≾ ε`    --
-- always holds, and the base's `u ≾ ε` makes every recursion's --
-- effect the unit. A countdown on three is refuted at three    --
-- ticks, although each of its runs takes three. A function is  --
-- usable in the step, `⊤ᵣ ≾ uᵣ` holding. Recursion inside an   --
-- operation clause is typed, but a clause dropping its         --
-- continuation after a countdown is refuted. On lists the      --
-- same: a head is usable whatever its type, a box among them.  --
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
open import TypeInference.Examples.Variables

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

------------------------------------------------------------------
-- 7. Pure recursion on lists

expected-length : Scheme
expected-length = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (|List| α₀ ⇒ Nat ‼ ûₑ) ‼ ûₑ

length-reported : schemeOf (infer [] length) ≡ just expected-length
length-reported = refl

expected-sum : Scheme
expected-sum = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (|List| Nat ⇒ Nat ‼ ûₑ) ‼ ûₑ

sum-reported : schemeOf (infer [] sum) ≡ just expected-sum
sum-reported = refl

inc-all-reported :
  schemeOf (infer [] inc-all) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ (|List| Nat ⇒ |List| Nat ‼ ûₑ) ‼ ûₑ)
inc-all-reported = refl

------------------------------------------------------------------
-- 8. The head in the step: `∣ ε ∣ ≾ uᵣ` holds at every grade, so
-- the head is usable whatever its type, a box among them

copy-reported :
  schemeOf (infer [] copy) ≡ just (∀[ 1 , 0 , 0 ] ⊤ ⟹ (|List| α₀ ⇒ |List| α₀ ‼ ûₑ) ‼ ûₑ)
copy-reported = refl

call-all-reported :
  schemeOf (infer [] call-all)
    ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ (|List| (Unit ⇒ Unit ‼ ûₑ) ⇒ Unit ‼ ûₑ) ‼ ûₑ)
call-all-reported = refl

expected-last-or : Scheme
expected-last-or =
  ∀[ 3 , 0 , 0 ] α₂ <: α₁ ∧ α₀ <: α₁ ⟹ (α₂ ⇒ (|List| α₀ ⇒ α₁ ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

last-or-reported : schemeOf (infer [] last-or) ≡ just expected-last-or
last-or-reported = refl

expected-last-box : Scheme
expected-last-box =
  ∀[ 0 , 1 , 0 ] ρ₀ ≾ᵣ ⌜ 1 ⌝ʳ ⟹
    ([ ρ₀ ] Nat ⇒ (|List| ([ ⌜ 1 ⌝ʳ ] Nat) ⇒ [ ρ₀ ] Nat ‼ ûₑ) ‼ ûₑ) ‼ ûₑ

last-box-reported : schemeOf (infer [] last-box) ≡ just expected-last-box
last-box-reported = refl

expected-latest : Scheme
expected-latest = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (|List| ([ ⌜ 1 ⌝ʳ ] Nat) ⇒ Nat ‼ ûₑ) ‼ ûₑ

latest-reported : schemeOf (infer [] latest) ≡ just expected-latest
latest-reported = refl

latest-ready-reported : schemeOf (infer [] latest-ready) ≡ just expected-latest
latest-ready-reported = refl

------------------------------------------------------------------
-- 9. A tick per element: the effect is the unit, so three ticks is
-- refuted

ticks-reported :
  schemeOf (infer [] ticks) ≡ just (∀[ 1 , 0 , 0 ] ⊤ ⟹ (|List| α₀ ⇒ Unit ‼ ûₑ) ‼ ûₑ)
ticks-reported = refl

ticks-at-3-verdict : infer [] (ticks-at 3) ≡ untypable
ticks-at-3-verdict = refl

ticks-at-3-not-typable : ¬ Typable [] (ticks-at 3)
ticks-at-3-not-typable = infer-untypable [] (ticks-at 3) ticks-at-3-verdict
