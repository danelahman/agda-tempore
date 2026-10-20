------------------------------------------------------------------------
-- Worked rigid timed regular upper bounds, in whole steps.           --
--                                                                    --
-- Heating takes two to four steps, cooling one or two, logging one.  --
-- The cases are those of the formalisation findings (F4), the order  --
-- of strict waits and budgets, the prototype's tests of the rigid    --
-- upper bounds, the window rule, the delays, and the costs of open   --
-- ends. Each comparison is established by running the inclusion      --
-- test.                                                              --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Regular.RightSided where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ)
open import Relation.Nullary using (¬_)
open import Data.Fin.Subset using (⁅_⁆; _∪_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Data.Product using (Σ; _×_; _,_)

open import Util.Equality

open import Syntax.Durations.Nat using (ℕᵀ; ℕᵀ-discrete)
open import Syntax.Durations.Intervals ℕᵀ
  using (Interval; ⟪_,_⟫; fin; ⁻; ⁺; _⊑?_; 0⁺; lo; inf; sup)
  renaming (_∣_ to _∣ᶜ_)
open import Syntax.Durations.Intervals.Dense ℕᵀ using (_∈ⁱ_; _∈ⁱ?_; inf-∈)
open import Syntax.Grades.Traces.RunningTimes ℕᵀ using (RunningTimes; Bounded)

data Op : Set where
  heat cool log : Op

code : Op → Fin 3
code heat = zero
code cool = suc zero
code log  = suc (suc zero)

name : Fin 3 → Op
name zero             = heat
name (suc zero)       = cool
name (suc (suc zero)) = log

name-code : ∀ o → name (code o) ≡ o
name-code heat = refl
name-code cool = refl
name-code log  = refl

code-name : ∀ c → code (name c) ≡ c
code-name zero             = refl
code-name (suc zero)       = refl
code-name (suc (suc zero)) = refl


rt : Op → Interval
rt heat = ⟪ 2 ∣ᶜ ⁻ , fin (4 ∣ᶜ ⁺) ⟫
rt cool = ⟪ 1 ∣ᶜ ⁻ , fin (2 ∣ᶜ ⁺) ⟫
rt log  = ⟪ 1 ∣ᶜ ⁻ , fin (1 ∣ᶜ ⁺) ⟫

running : RunningTimes Op
running = record
  { rt          = rt
  ; rt-bounded  = λ { heat → Bounded.fin (4 ∣ᶜ ⁺) ; cool → Bounded.fin (2 ∣ᶜ ⁺) ; log → Bounded.fin (1 ∣ᶜ ⁺) }
  ; rt-positive = λ { heat → toWitness {a? = 0⁺ ⊑? lo (rt heat)} _
                    ; cool → toWitness {a? = 0⁺ ⊑? lo (rt cool)} _
                    ; log  → toWitness {a? = 0⁺ ⊑? lo (rt log)} _ }
  ; rt-inhabited = λ { heat → 2 , toWitness {a? = 2 ∈ⁱ? rt heat} _
                     ; cool → 1 , toWitness {a? = 1 ∈ⁱ? rt cool} _
                     ; log  → 1 , toWitness {a? = 1 ∈ⁱ? rt log} _ }
  }

open import Syntax.Grades.Example.Traces.Rigid.Regular.RightSided Op 3 code name name-code code-name running


------------------------------------------------------------------------
-- Upper bounds and runs

-- a run's operations and delays, graded on this side

‵ᵍ_ : Op → Closed
‵ᵍ heat = ⌜ ‵_ {upper} heat ⌝
‵ᵍ cool = ⌜ ‵_ {upper} cool ⌝
‵ᵍ log = ⌜ ‵_ {upper} log ⌝

infix 9 ‵ᵍ_

_·ᵍ_ : Closed → Closed → Closed
_·ᵍ_ = C._·_

infixl 7 _·ᵍ_

------------------------------------------------------------------------
-- The bounds and runs compared below, each named, so that a comparison
-- is checked by running the inclusion test once

one one·one wait-around budget-5 wait-5 heat-then-budget heat-wait-budget
  heat-budget-3 heat-then-cool heat-strict-cool across within-cool-and-log
  within-cool-then-log logged-run uncooled-run stirred-run wait-two
  two-delays : Closed
one                  = ⌜ ≤ 1 ⌝
one·one              = one ·ᵍ one
wait-around          = ⌜ ≤ 1 · !≤ 1 · ≤ 1 ⌝
budget-5          = ⌜ ≤ 5 ⌝
wait-5          = ⌜ !≤ 5 ⌝
heat-then-budget     = ⌜ ‵ heat · ≤ 5 ⌝
heat-wait-budget     = ⌜ ‵ heat · !≤ 2 · ≤ 3 ⌝
heat-budget-3        = ⌜ ‵ heat · ≤ 3 ⌝
heat-then-cool       = ⌜ ‵ heat · ≤ 3 · ‵ cool ⌝
heat-strict-cool     = ⌜ ‵ heat · !≤ 3 · ‵ cool ⌝
across               = ‵ᵍ cool
within-cool-and-log  = ⌜ (≤ 1 & ⁅ code cool ⁆) · (≤ 1 & (⁅ code cool ⁆ ∪ ⁅ code log ⁆)) ⌝
within-cool-then-log = ⌜ (≤ 1 & ⁅ code cool ⁆) · (≤ 1 & ⁅ code log ⁆) ⌝
logged-run           = ‵ᵍ heat ·ᵍ ‵ᵍ log ·ᵍ of-dur 2 ·ᵍ ‵ᵍ cool
uncooled-run         = ‵ᵍ heat ·ᵍ of-dur 3
stirred-run          = ‵ᵍ heat ·ᵍ of-dur 2 ·ᵍ ‵ᵍ log ·ᵍ ‵ᵍ cool
wait-two             = ⌜ !≤ 2 ⌝
two-delays           = of-dur 1 ·ᵍ of-dur 1

------------------------------------------------------------------------
-- F4: sequencing two budgets of one keeps within two budgets of one
-- around a strict wait, which may be empty; and an operation of two
-- steps fits them too

f4 : C._≾_ one·one wait-around
f4 = holds one·one wait-around refl

two-steps-fit : C._≾_ (‵ᵍ cool) wait-around
two-steps-fit = holds (‵ᵍ cool) wait-around refl

------------------------------------------------------------------------
-- The kinds of stretch: a strict wait lies below a budget, not the
-- converse; an unused strict wait is passed over

strict-below-budget : C._≾_ wait-5 budget-5
strict-below-budget = holds wait-5 budget-5 refl

budget-not-below-strict : ¬ C._≾_ budget-5 wait-5
budget-not-below-strict = fails budget-5 wait-5 refl

wait-then-budget : C._≾_ heat-wait-budget heat-then-budget
wait-then-budget = holds heat-wait-budget heat-then-budget refl

wait-skipped : C._≾_ heat-budget-3 heat-wait-budget
wait-skipped = holds heat-budget-3 heat-wait-budget refl

budget-not-in-wait : ¬ C._≾_ heat-then-budget heat-wait-budget
budget-not-in-wait = fails heat-then-budget heat-wait-budget refl

------------------------------------------------------------------------
-- The prototype's tests (`traces_rigid_upper_reject.tpe`,
-- `strict_delays_traces_reject.tpe`)

-- a log bought within the delay between heating and cooling

logged : C._≾_ logged-run heat-then-cool
logged = holds logged-run heat-then-cool refl

-- the cooling of the bound is not left out

uncooled : ¬ C._≾_ uncooled-run heat-then-cool
uncooled = fails uncooled-run heat-then-cool refl

-- an operation of one step after a wait of two fits a budget of three,
-- but not a strict wait (the stirring of the prototype's test)

stirred-budget : C._≾_ stirred-run heat-then-cool
stirred-budget = holds stirred-run heat-then-cool refl

stirred-strict : ¬ C._≾_ stirred-run heat-strict-cool
stirred-strict = fails stirred-run heat-strict-cool refl

------------------------------------------------------------------------
-- The window rule: an operation the bound does not match belongs to
-- the set of every stretch it overlaps

across-two-windows : C._≾_ across within-cool-and-log
across-two-windows = holds across within-cool-and-log refl

into-a-window-without-it : ¬ C._≾_ across within-cool-then-log
into-a-window-without-it = fails across within-cool-then-log refl

------------------------------------------------------------------------
-- A delay of two steps is a wait of at most two, as two delays of one
-- are

of-dur-2 : C._≾_ (of-dur 2) wait-two
of-dur-2 = holds (of-dur 2) wait-two refl

of-dur-2′ : C._≾_ wait-two (of-dur 2)
of-dur-2′ = holds wait-two (of-dur 2) refl

of-dur-1+1 : C._≾_ wait-two two-delays
of-dur-1+1 = holds wait-two two-delays refl

------------------------------------------------------------------------
-- Costs in whole steps: an open end admits the adjacent step, so
-- `]0,2[` costs one step at both ends, and `]1,2[` admits none

open-costs : inf (0 ∣ᶜ ⁺) ≡ 1 × sup (2 ∣ᶜ ⁻) ≡ 1
open-costs = refl , refl

open-empty : ¬ Σ ℕ (_∈ⁱ ⟪ 1 ∣ᶜ ⁺ , fin (2 ∣ᶜ ⁻) ⟫)
open-empty (_ , m) =
  toWitnessFalse {a? = 2 ∈ⁱ? ⟪ 1 ∣ᶜ ⁺ , fin (2 ∣ᶜ ⁻) ⟫} _ (inf-∈ ℕᵀ-discrete m)
