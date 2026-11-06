------------------------------------------------------------------------
-- Worked rational timed regex lower bounds.                          --
--                                                                    --
-- The operations of `TimedRegex.Finite.Operations`. The cases: waits --
-- add up under iteration; the empty word is no wait; activity needs  --
-- explicit flanks, here iterated; open against closed ends under     --
-- iteration; the Kleene plus; the hull of a delay; and an idle wait  --
-- made only from a time span admitting every operation.              --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.TimedRegex.Rational.LowerBound where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Product using (_×_; _,_)

open import Util.Equality

open import Grades.Examples.Time.Rational.Interval using (_/_; #_)
open import Grades.Examples.Worked.Traces.TimedRegex.Finite.Operations
open import Grades.Examples.Traces.TimedRegex.Rational.LowerBound Op 3 code name name-code code-name running

L : OpSet
L = ⁅ code log ⁆

------------------------------------------------------------------------
-- Waits add up under iteration; iterating admits the empty word

waits-iterated : holds ⌜ idle ≥ (# 1) · idle ≥ (# 1) ⌝ ⌜ (idle ≥ (# 1)) * ⌝ ≡ true
               × holds ⌜ (idle ≥ (# 1)) * ⌝ ⌜ idle ≥ (# 1) ⌝ ≡ false
waits-iterated = refl , refl

-- at least one wait of at least a unit is a wait of at least a unit
waits-plus : holds (⌜ idle ≥ (# 1) ⌝ ⁺ᵉ) ⌜ idle ≥ (# 1) ⌝ ≡ true
           × holds ⌜ idle ≥ (# 1) ⌝ (⌜ idle ≥ (# 1) ⌝ ⁺ᵉ) ≡ true
waits-plus = refl , refl

------------------------------------------------------------------------
-- Logs, iterated, within a time span admitting them; an interrupting
-- operation needs its own flanks

logs-in-stretch : holds ⌜ ‵ log * ⌝ ⌜ ≥ (# 0) & L ⌝ ≡ true
logs-in-stretch = refl

heat-interrupts : holds ⌜ ‵ log * · ‵ heat ⌝ ⌜ ≥ (# 0) & L ⌝ ≡ false
heat-interrupts = refl

flanked : holds ⌜ (‵ log · ‵ heat) * ⌝ ⌜ ((≥ (# 0) & L) · ‵ heat) * ⌝ ≡ true
flanked = refl

------------------------------------------------------------------------
-- Open and closed ends under iteration: two logs take more than half a
-- unit, at least one more than a quarter

two-logs : holds ⌜ ‵ log · ‵ log ⌝ ⌜ > (1 / 2) & L ⌝ ≡ true
two-logs = refl

logs-plus-open : holds (⌜ ‵ log ⌝ ⁺ᵉ) ⌜ > (1 / 4) & L ⌝ ≡ true
               × holds (⌜ ‵ log ⌝ ⁺ᵉ) ⌜ > (1 / 2) & L ⌝ ≡ false
logs-plus-open = refl , refl

------------------------------------------------------------------------
-- The hull of a delay

delay-zero : holds (waitᴸ (# 0)) ⌜ ε ⌝ ≡ true × holds ⌜ ε ⌝ (waitᴸ (# 0)) ≡ true
delay-zero = refl , refl

delay-iterated : holds (waitᴸ (# 2)) ⌜ (idle ≥ (1 / 2)) * ⌝ ≡ true
delay-iterated = refl

------------------------------------------------------------------------
-- An idle wait is made only from a time span admitting every operation:
-- `idle ‵ heat` is refused

heat-not-span : span? (‵ heat) ≡ false
heat-not-span = refl
