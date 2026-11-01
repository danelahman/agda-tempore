------------------------------------------------------------------------
-- Primitive recursion at left-sided intervals                        --
--                                                                    --
-- The unit is the top, so every recursion's effect is the unit, and  --
-- a countdown on three annotated at three ticks is refuted.          --
-- Functions and heads of any type are usable in the step. A clause   --
-- that drops its continuation after a countdown is refuted.          --
------------------------------------------------------------------------

open import Data.Maybe.Base using (just)

open import Relation.Nullary using (¬_)

open import Grades.Durations.Nat using (ℕᴰ-stepped)

open import Util.Equality

open import PolymorphicCalculus.Examples.Specs using (module Time-LeftSided)

module PolymorphicCalculus.Examples.Recursion.Time.LeftSided where

open Time-LeftSided using (spec; hints; enum)

open import PolymorphicCalculus.Syntax.Grades   spec
open import PolymorphicCalculus.Syntax.Types    spec
open import PolymorphicCalculus.Syntax.Contexts spec using ([])
open import PolymorphicCalculus.Inference.Principality spec using (Typable; untypable)
open import PolymorphicCalculus.Inference.SolverImpl spec hints enum using (infer-untypable)
open import PolymorphicCalculus.Examples.Recursion spec hints enum ℕᴰ-stepped
open import PolymorphicCalculus.Examples.Variables

------------------------------------------------------------------
-- 1. Pure recursion

expected-add : Scheme
expected-add = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (nat ⇒ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

add-reported : schemeOf (infer [] add) ≡ just expected-add
add-reported = refl

------------------------------------------------------------------
-- 2. The predecessor, and an outer natural number, in the step

expected-rebuild : Scheme
expected-rebuild = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

rebuild-reported : schemeOf (infer [] rebuild) ≡ just expected-rebuild
rebuild-reported = refl

mul-reported : schemeOf (infer [] mul) ≡ just expected-add
mul-reported = refl

------------------------------------------------------------------
-- 3. A function from outside the step: usable

expected-each : Scheme
expected-each =
  ∀[ 0 , 0 , 0 ] ⊤ ⟹ ((unit ⇒ unit ! 𝟏̂ₑ) ⇒ (nat ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

each-reported : schemeOf (infer [] each) ≡ just expected-each
each-reported = refl

------------------------------------------------------------------
-- 4. A countdown: the effect is the unit

expected-countdown : Scheme
expected-countdown = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (nat ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ

countdown-reported : schemeOf (infer [] countdown) ≡ just expected-countdown
countdown-reported = refl

countdown-at-0-reported :
  schemeOf (infer [] (countdown-at 0)) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! 𝟏̂ₑ)
countdown-at-0-reported = refl

-- annotated at three ticks: refuted, the base forcing the unit

countdown-at-3-verdict : infer [] (countdown-at 3) ≡ untypable
countdown-at-3-verdict = refl

countdown-at-3-not-typable : ¬ Typable [] (countdown-at 3)
countdown-at-3-not-typable = infer-untypable [] (countdown-at 3) countdown-at-3-verdict

------------------------------------------------------------------
-- 5. Recursion inside an operation clause: typed and established

in-clause-pure-reported :
  schemeOf (infer [] in-clause-pure) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! 𝟏̂ₑ)
in-clause-pure-reported = refl

in-clause-tick-reported :
  schemeOf (infer [] in-clause-tick) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ unit ! 𝟏̂ₑ)
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
expected-length = ∀[ 1 , 0 , 0 ] ⊤ ⟹ (list α₀ ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

length-reported : schemeOf (infer [] length) ≡ just expected-length
length-reported = refl

expected-sum : Scheme
expected-sum = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (list nat ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

sum-reported : schemeOf (infer [] sum) ≡ just expected-sum
sum-reported = refl

inc-all-reported :
  schemeOf (infer [] inc-all) ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ (list nat ⇒ list nat ! 𝟏̂ₑ) ! 𝟏̂ₑ)
inc-all-reported = refl

------------------------------------------------------------------
-- 8. The head in the step: usable whatever its type

copy-reported :
  schemeOf (infer [] copy) ≡ just (∀[ 1 , 0 , 0 ] ⊤ ⟹ (list α₀ ⇒ list α₀ ! 𝟏̂ₑ) ! 𝟏̂ₑ)
copy-reported = refl

call-all-reported :
  schemeOf (infer [] call-all)
    ≡ just (∀[ 0 , 0 , 0 ] ⊤ ⟹ (list (unit ⇒ unit ! 𝟏̂ₑ) ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ)
call-all-reported = refl

expected-last-or : Scheme
expected-last-or =
  ∀[ 3 , 0 , 0 ] α₂ <: α₁ ∧ α₀ <: α₁ ⟹ (α₂ ⇒ (list α₀ ⇒ α₁ ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

last-or-reported : schemeOf (infer [] last-or) ≡ just expected-last-or
last-or-reported = refl

expected-last-box : Scheme
expected-last-box =
  ∀[ 0 , 1 , 0 ] ρ₀ ≾ᵣ ⌜ 1 ⌝ʳ ⟹
    ([ ρ₀ ] nat ⇒ (list ([ ⌜ 1 ⌝ʳ ] nat) ⇒ [ ρ₀ ] nat ! 𝟏̂ₑ) ! 𝟏̂ₑ) ! 𝟏̂ₑ

last-box-reported : schemeOf (infer [] last-box) ≡ just expected-last-box
last-box-reported = refl

expected-latest : Scheme
expected-latest = ∀[ 0 , 0 , 0 ] ⊤ ⟹ (list ([ ⌜ 1 ⌝ʳ ] nat) ⇒ nat ! 𝟏̂ₑ) ! 𝟏̂ₑ

latest-reported : schemeOf (infer [] latest) ≡ just expected-latest
latest-reported = refl

latest-ready-reported : schemeOf (infer [] latest-ready) ≡ just expected-latest
latest-ready-reported = refl

------------------------------------------------------------------
-- 9. A tick per element: the unit, so three ticks is refuted

ticks-reported :
  schemeOf (infer [] ticks) ≡ just (∀[ 1 , 0 , 0 ] ⊤ ⟹ (list α₀ ⇒ unit ! 𝟏̂ₑ) ! 𝟏̂ₑ)
ticks-reported = refl

ticks-at-3-verdict : infer [] (ticks-at 3) ≡ untypable
ticks-at-3-verdict = refl

ticks-at-3-not-typable : ¬ Typable [] (ticks-at 3)
ticks-at-3-not-typable = infer-untypable [] (ticks-at 3) ticks-at-3-verdict
