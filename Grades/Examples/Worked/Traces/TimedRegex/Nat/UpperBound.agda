------------------------------------------------------------------------
-- Worked timed regex upper bounds, in whole steps.                   --
--                                                                    --
-- Heating takes two to four steps, cooling one or two, logging one.  --
-- The cases: sequenced spans, the order of idle waits and            --
-- spans, rejected runs, the window rule, the delays, and the costs   --
-- of open ends. Each comparison is established by running the        --
-- inclusion test.                                                    --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.TimedRegex.Nat.UpperBound where

open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (ℕ)
open import Relation.Nullary using (¬_)
open import Data.Fin.Subset using (⁅_⁆; _∪_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Data.Product using (Σ; _×_; _,_)

open import Util.Equality

open import Grades.Durations.Nat using (ℕᵀ; ℕᵀ-discrete)
open import Grades.Durations.Intervals ℕᵀ
  using (Interval; ⟪_,_⟫; fin; ⁻; ⁺; _⊑?_; 0⁺; lo; inf; sup)
  renaming (_∣_ to _∣ᶜ_)
open import Grades.Durations.Intervals.Dense ℕᵀ using (_∈ⁱ_; _∈ⁱ?_; inf-∈)
open import Grades.Traces.RunningTimes ℕᵀ using (RunningTimes; Bounded)

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

open import Grades.Examples.Traces.TimedRegex.Nat.UpperBound Op 3 code name name-code code-name running


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

one one·one wait-around span-5 wait-5 heat-then-span heat-wait-span
  heat-span-3 heat-then-cool heat-idle-cool across within-cool-and-log
  within-cool-then-log logged-run uncooled-run stirred-run wait-two
  two-delays : Closed
one                  = ⌜ ≤ 1 ⌝
one·one              = one ·ᵍ one
wait-around          = ⌜ ≤ 1 · idle ≤ 1 · ≤ 1 ⌝
span-5               = ⌜ ≤ 5 ⌝
wait-5               = ⌜ idle ≤ 5 ⌝
heat-then-span       = ⌜ ‵ heat · ≤ 5 ⌝
heat-wait-span       = ⌜ ‵ heat · idle ≤ 2 · ≤ 3 ⌝
heat-span-3          = ⌜ ‵ heat · ≤ 3 ⌝
heat-then-cool       = ⌜ ‵ heat · ≤ 3 · ‵ cool ⌝
heat-idle-cool       = ⌜ ‵ heat · idle ≤ 3 · ‵ cool ⌝
across               = ‵ᵍ cool
within-cool-and-log  = ⌜ (≤ 1 & ⁅ code cool ⁆) · (≤ 1 & (⁅ code cool ⁆ ∪ ⁅ code log ⁆)) ⌝
within-cool-then-log = ⌜ (≤ 1 & ⁅ code cool ⁆) · (≤ 1 & ⁅ code log ⁆) ⌝
logged-run           = ‵ᵍ heat ·ᵍ ‵ᵍ log ·ᵍ ι 2 ·ᵍ ‵ᵍ cool
uncooled-run         = ‵ᵍ heat ·ᵍ ι 3
stirred-run          = ‵ᵍ heat ·ᵍ ι 2 ·ᵍ ‵ᵍ log ·ᵍ ‵ᵍ cool
wait-two             = ⌜ idle ≤ 2 ⌝
two-delays           = ι 1 ·ᵍ ι 1

------------------------------------------------------------------------
-- Sequencing two spans of one keeps within two spans of one
-- around an idle wait, which may be empty; and an operation of two
-- steps fits them too

spans-fit : C._≾_ one·one wait-around
spans-fit = holds one·one wait-around refl

two-steps-fit : C._≾_ (‵ᵍ cool) wait-around
two-steps-fit = holds (‵ᵍ cool) wait-around refl

------------------------------------------------------------------------
-- The kinds of time span: an idle wait lies below a span, not the
-- converse; an unused idle wait is passed over

idle-below-span : C._≾_ wait-5 span-5
idle-below-span = holds wait-5 span-5 refl

span-not-below-idle : ¬ C._≾_ span-5 wait-5
span-not-below-idle = fails span-5 wait-5 refl

wait-then-span : C._≾_ heat-wait-span heat-then-span
wait-then-span = holds heat-wait-span heat-then-span refl

wait-skipped : C._≾_ heat-span-3 heat-wait-span
wait-skipped = holds heat-span-3 heat-wait-span refl

span-not-in-wait : ¬ C._≾_ heat-then-span heat-wait-span
span-not-in-wait = fails heat-then-span heat-wait-span refl

------------------------------------------------------------------------
-- Rejected runs

-- a log bought within the delay between heating and cooling

logged : C._≾_ logged-run heat-then-cool
logged = holds logged-run heat-then-cool refl

-- the cooling of the bound is not left out

uncooled : ¬ C._≾_ uncooled-run heat-then-cool
uncooled = fails uncooled-run heat-then-cool refl

-- an operation of one step after a wait of two fits a span of three,
-- but not an idle wait

stirred-span : C._≾_ stirred-run heat-then-cool
stirred-span = holds stirred-run heat-then-cool refl

stirred-idle : ¬ C._≾_ stirred-run heat-idle-cool
stirred-idle = fails stirred-run heat-idle-cool refl

------------------------------------------------------------------------
-- The window rule: an operation the bound does not match belongs to the
-- set of every time span it overlaps

across-two-windows : C._≾_ across within-cool-and-log
across-two-windows = holds across within-cool-and-log refl

into-a-window-without-it : ¬ C._≾_ across within-cool-then-log
into-a-window-without-it = fails across within-cool-then-log refl

------------------------------------------------------------------------
-- A delay of two steps is a wait of at most two, as two delays of one
-- are

ι-2 : C._≾_ (ι 2) wait-two
ι-2 = holds (ι 2) wait-two refl

ι-2′ : C._≾_ wait-two (ι 2)
ι-2′ = holds wait-two (ι 2) refl

ι-1+1 : C._≾_ wait-two two-delays
ι-1+1 = holds wait-two two-delays refl

------------------------------------------------------------------------
-- Costs in whole steps: an open end admits the adjacent step, so
-- `]0,2[` costs one step at both ends, and `]1,2[` admits none

open-costs : inf (0 ∣ᶜ ⁺) ≡ 1 × sup (2 ∣ᶜ ⁻) ≡ 1
open-costs = refl , refl

open-empty : ¬ Σ ℕ (_∈ⁱ ⟪ 1 ∣ᶜ ⁺ , fin (2 ∣ᶜ ⁻) ⟫)
open-empty (_ , m) =
  toWitnessFalse {a? = 2 ∈ⁱ? ⟪ 1 ∣ᶜ ⁺ , fin (2 ∣ᶜ ⁻) ⟫} _ (inf-∈ ℕᵀ-discrete m)
