------------------------------------------------------------------------
-- Worked finite timed regex upper bounds in rational time.           --
--                                                                    --
-- Heating takes two to four units, cooling more than one and less    --
-- than two, logging more than a quarter and at most a half. The      --
-- cases: products of spans at rational lengths, open against         --
-- closed ends, an equivalence of distinct expressions, the window    --
-- rule, open running times, and the hull of a delay. Each comparison --
-- is checked by evaluating the decision.                             --
--                                                                    --
-- The product does not commute, and the unit is not least.           --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.TimedRegex.Finite.UpperBound where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (False; toWitnessFalse)

open import Util.Equality

open import Grades.Examples.Time.Rational.Interval using (_/_; #_)
open import Grades.Examples.Worked.Traces.TimedRegex.Finite.Operations
open import Grades.Examples.Traces.TimedRegex.Finite.UpperBound Op 3 code name name-code code-name running

open import Grades.Base using (module Grade)

private
  module G = Grade upper-bound

------------------------------------------------------------------------
-- An "at most" idle wait does not separate spans on its own

two-halves separated : Proper′ upper
two-halves = ⌜ ≤ (1 / 2) · ≤ (1 / 2) ⌝
separated  = ⌜ ≤ (1 / 2) · idle ≤ (1 / 2) · ≤ (1 / 2) ⌝

-- the idle wait is passed at length zero
halves-within-separated : holds two-halves separated ≡ true
halves-within-separated = refl

separated-not-within-halves : holds separated two-halves ≡ false
separated-not-within-halves = refl

-- cooling, less than two units, spreads over both spans past the wait
cool-in-spans : holds ⌜ ‵ cool ⌝ ⌜ ≤ (# 1) · idle ≤ (# 1) · ≤ (# 1) ⌝ ≡ true
cool-in-spans = refl

heat-too-long : holds ⌜ ‵ heat ⌝ ⌜ ≤ (# 1) · idle ≤ (# 1) · ≤ (# 1) ⌝ ≡ false
heat-too-long = refl

------------------------------------------------------------------------
-- Open and closed ends

open-below-closed : holds ⌜ idle < (# 1) ⌝ ⌜ idle ≤ (# 1) ⌝ ≡ true
open-below-closed = refl

closed-not-below-open : holds ⌜ idle ≤ (# 1) ⌝ ⌜ idle < (# 1) ⌝ ≡ false
closed-not-below-open = refl

-- distinct expressions with the same runs: the wait's last instant can
-- be taken by the open span after it, whose set includes the wait's
same-runs : holds ⌜ idle ≤ (# 1) · (< (# 1) & ⁅ code log ⁆) ⌝ ⌜ idle < (# 1) · (< (# 1) & ⁅ code log ⁆) ⌝ ≡ true
          × holds ⌜ idle < (# 1) · (< (# 1) & ⁅ code log ⁆) ⌝ ⌜ idle ≤ (# 1) · (< (# 1) & ⁅ code log ⁆) ⌝ ≡ true
same-runs = refl , refl

------------------------------------------------------------------------
-- The window rule: an operation spanning time spans belongs to each

log-across : holds ⌜ ‵ log ⌝ ⌜ (≤ (1 / 4) & ⁅ code log ⁆) · (≤ (1 / 4) & ⁅ code log ⁆) ⌝ ≡ true
log-across = refl

log-into-wait : holds ⌜ ‵ log ⌝ ⌜ (≤ (1 / 4) & ⁅ code log ⁆) · idle ≤ (1 / 4) ⌝ ≡ false
log-into-wait = refl

------------------------------------------------------------------------
-- Open running times

cool-in-open : holds ⌜ ‵ cool ⌝ ⌜ < (# 2) & ⁅ code cool ⁆ ⌝ ≡ true
cool-in-open = refl

cool-too-long : holds ⌜ ‵ cool ⌝ ⌜ < (3 / 2) & ⁅ code cool ⁆ ⌝ ≡ false
cool-too-long = refl

-- a union is below a bound when each of its words is
either : holds ⌜ ‵ heat ∣ ‵ cool ⌝ ⌜ ≤ (# 4) ⌝ ≡ true
either = refl

maybe-log : holds ⌜ log ˀ ⌝ ⌜ ≤ (1 / 2) & ⁅ code log ⁆ ⌝ ≡ true
maybe-log = refl

------------------------------------------------------------------------
-- The hull of a delay

delay-within : holds (waitᵁ (3 / 2)) ⌜ ≤ (# 2) ⌝ ≡ true
delay-within = refl

delay-past-open : holds (waitᵁ (3 / 2)) ⌜ idle < (3 / 2) ⌝ ≡ false
delay-past-open = refl

------------------------------------------------------------------------
-- Failures of commutativity and of the unit being least, as
-- comparisons of the grade, established by its decision

fails : (c d : G.Carrier) {p : False (c G.≾? d)} → ¬ (c G.≾ d)
fails c d {p} = toWitnessFalse p

-- heating and then cooling is not cooling and then heating

not-commutative : ¬ (⌜ ‵ heat ⌝ G.· ⌜ ‵ cool ⌝ G.≾ ⌜ ‵ cool ⌝ G.· ⌜ ‵ heat ⌝)
not-commutative = fails (⌜ ‵ heat ⌝ G.· ⌜ ‵ cool ⌝) (⌜ ‵ cool ⌝ G.· ⌜ ‵ heat ⌝)

-- the empty run is not a run of heating

unit-not-least : ¬ (G.𝟏 G.≾ ⌜ ‵ heat ⌝)
unit-not-least = fails G.𝟏 ⌜ ‵ heat ⌝
