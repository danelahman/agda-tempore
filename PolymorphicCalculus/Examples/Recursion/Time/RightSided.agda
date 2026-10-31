------------------------------------------------------------------
-- Primitive recursion at right-sided intervals                 --
--                                                              --
-- `ε · ε ≾ ε` holds only at the unit and the top: a pure       --
-- recursion has the unit, one ticking per step the top,        --
-- refuted at any finite bound, in a clause too. Functions are  --
-- not usable in the step; with a tick per step, heads must be  --
-- eternal.                                                     --
------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)
open import Grades.Base using (module GradeSystemInterface)
open import Language.Spec using (LanguageSpec)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-RightSided)

module PolymorphicCalculus.Examples.Recursion.Time.RightSided where

open Time-RightSided using (spec; hints; enum)
open GradeSystemInterface (LanguageSpec.Grades spec) using (⊤ᵣ; ⊤ₑ)

open import PolymorphicCalculus.Syntax.Grades   spec
open import PolymorphicCalculus.Syntax.Types    spec
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Recursion spec hints enum ℕᴰ-stepped
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- 1. Pure recursion: the effect is lowered to the unit

expected-add : Scheme
expected-add = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (nat ⇒ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

add-reported : schemeOf (infer [] add) ≡ just expected-add
add-reported = refl

add-verdict : verdict (check [] add) ≡ established
add-verdict = refl

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step

expected-rebuild : Scheme
expected-rebuild = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

rebuild-reported : schemeOf (infer [] rebuild) ≡ just expected-rebuild
rebuild-reported = refl

-- both recursions' effects the unit

mul-reported : schemeOf (infer [] mul) ≡ just expected-add
mul-reported = refl

mul-verdict : verdict (check [] mul) ≡ established
mul-verdict = refl

------------------------------------------------------------------
-- 3. A function from outside the step: `⊤ᵣ ≾ 𝟏ᵣ` fails

each-verdict : infer [] each ≡ untypable
each-verdict = refl

each-not-typable : ¬ Typable [] each
each-not-typable = infer-untypable [] each each-verdict

------------------------------------------------------------------
-- 4. A countdown: the top, the closure of a tick

expected-countdown : Scheme
expected-countdown = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (nat ⇒ unit ! econst ⊤ₑ) ! 𝟏̂ₑ

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

-- annotated at three ticks: `⊤ ≾ ⌜ 3 ⌝` is closed and false

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
-- 5. Recursion inside a clause: a pure step gives the unit; a tick a
-- step the top, which no finite bound admits

in-clause-pure-reported :
  schemeOf (infer [] in-clause-pure) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! 𝟏̂ₑ)
in-clause-pure-reported = refl

in-clause-pure-check : verdict (check [] in-clause-pure) ≡ established
in-clause-pure-check = refl

in-clause-tick-verdict : infer [] in-clause-tick ≡ untypable
in-clause-tick-verdict = refl

in-clause-tick-not-typable : ¬ Typable [] in-clause-tick
in-clause-tick-not-typable = infer-untypable [] in-clause-tick in-clause-tick-verdict

------------------------------------------------------------------
-- 6. A clause dropping its continuation: for `read`, the closed
-- `⌜ 1 ⌝ · ⌜ 1 ⌝ ≾ ⌜ 1 ⌝` is false

drop-clause-verdict : infer [] drop-clause ≡ untypable
drop-clause-verdict = refl

drop-clause-check : verdict (check [] drop-clause) ≡ untypable
drop-clause-check = refl

drop-clause-not-typable : ¬ Typable [] drop-clause
drop-clause-not-typable = infer-untypable [] drop-clause drop-clause-verdict

------------------------------------------------------------------
-- 7. Pure recursion on lists: the effect is the unit

expected-length : Scheme
expected-length = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (list α₀ ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

length-reported : schemeOf (infer [] length) ≡ just expected-length
length-reported = refl

expected-sum : Scheme
expected-sum = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (list nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

sum-reported : schemeOf (infer [] sum) ≡ just expected-sum
sum-reported = refl

sum-verdict : verdict (check [] sum) ≡ established
sum-verdict = refl

expected-inc-all : Scheme
expected-inc-all = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (list nat ⇒ list nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

inc-all-reported : schemeOf (infer [] inc-all) ≡ just expected-inc-all
inc-all-reported = refl

------------------------------------------------------------------
-- 8. The head: any type with a pure step, eternal with a tick a step
-- (boxes refused); unboxed, its box needs the top grade

expected-copy : Scheme
expected-copy = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (list α₀ ⇒ list α₀ ! 𝟏̂ₑ) ! 𝟏̂ₑ

copy-reported : schemeOf (infer [] copy) ≡ just expected-copy
copy-reported = refl

expected-call-all : Scheme
expected-call-all = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (list (unit ⇒ unit ! 𝟏̂ₑ) ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ

call-all-reported : schemeOf (infer [] call-all) ≡ just expected-call-all
call-all-reported = refl

expected-last-or : Scheme
expected-last-or =
  ∀[ 3 , 0 , 0 ] eternal α₀ ∧ α₂ <: α₁ ∧ α₀ <: α₁ ⟹
    (α₂ ⇒ (list α₀ ⇒ α₁ ! econst ⊤ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

last-or-reported : schemeOf (infer [] last-or) ≡ just expected-last-or
last-or-reported = refl

last-box-verdict : infer [] last-box ≡ untypable
last-box-verdict = refl

last-box-not-typable : ¬ Typable [] last-box
last-box-not-typable = infer-untypable [] last-box last-box-verdict

expected-latest : Scheme
expected-latest =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ (list ([ rconst ⊤ᵣ ] nat) ⇒ nat ! econst ⊤ₑ) ! 𝟏̂ₑ

latest-reported : schemeOf (infer [] latest) ≡ just expected-latest
latest-reported = refl

latest-ready-verdict : infer [] latest-ready ≡ untypable
latest-ready-verdict = refl

latest-ready-not-typable : ¬ Typable [] latest-ready
latest-ready-not-typable = infer-untypable [] latest-ready latest-ready-verdict

------------------------------------------------------------------
-- 9. A tick per element: the top; refuted at three ticks

expected-ticks : Scheme
expected-ticks = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (list α₀ ⇒ unit ! econst ⊤ₑ) ! 𝟏̂ₑ

ticks-reported : schemeOf (infer [] ticks) ≡ just expected-ticks
ticks-reported = refl

ticks-verdict : verdict (check [] ticks) ≡ established
ticks-verdict = refl

ticks-top-verdict : verdict (check [] ticks-top) ≡ established
ticks-top-verdict = refl

ticks-at-3-verdict : infer [] (ticks-at 3) ≡ untypable
ticks-at-3-verdict = refl

ticks-at-3-not-typable : ¬ Typable [] (ticks-at 3)
ticks-at-3-not-typable = infer-untypable [] (ticks-at 3) ticks-at-3-verdict

------------------------------------------------------------------
-- 10. Calling the recursive result twice: the latent effect is the
-- top, and the argument, used after a call, must be eternal

expected-twice : Scheme
expected-twice =
  ∀[ 1 , 0 , 0 ] eternal α₀ ⟹
    (nat ⇒ ([ rconst ⊤ᵣ ] (α₀ ⇒ unit ! econst ⊤ₑ)) ! 𝟏̂ₑ) ! 𝟏̂ₑ

twice-reported : schemeOf (infer [] twice) ≡ just expected-twice
twice-reported = refl

expected-twice-run : Scheme
expected-twice-run = ∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! econst ⊤ₑ

twice-run-reported : schemeOf (infer [] twice-run) ≡ just expected-twice-run
twice-run-reported = refl

twice-run-verdict : verdict (check [] twice-run) ≡ established
twice-run-verdict = refl

-- annotated at one tick: refuted

twice-run-at-1-verdict : infer [] (twice-run-at 1) ≡ untypable
twice-run-at-1-verdict = refl

twice-run-at-1-not-typable : ¬ Typable [] (twice-run-at 1)
twice-run-at-1-not-typable = infer-untypable [] (twice-run-at 1) twice-run-at-1-verdict
