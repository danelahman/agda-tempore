------------------------------------------------------------------------
-- Worked rigid timed finite-expression lower bounds in dense time.   --
--                                                                    --
-- The operations of `Operations`. The cases: idle waits add up,      --
-- undisturbed waits are kept, activity needs explicit flanks, open   --
-- against closed ends, an equivalence of distinct expressions, the   --
-- hull of a delay, and an idle wait made only from a span letter.    --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.TimedRegex.Finite.LowerBound where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Product using (_×_; _,_)

open import Util.Equality

open import Grades.Examples.Time.Rational.Interval using (_/_; #_)
open import Grades.Examples.Worked.Traces.TimedRegex.Finite.Operations
open import Grades.Examples.Traces.TimedRegex.Finite.LowerBound Op 3 code name name-code code-name running

------------------------------------------------------------------------
-- Idle waits add up, and undisturbed waits are kept

waits-add : holds ⌜ idle ≥ (# 2) · idle ≥ (# 3) ⌝ ⌜ idle ≥ (# 5) ⌝ ≡ true
          × holds ⌜ idle ≥ (# 5) ⌝ ⌜ idle ≥ (# 2) · idle ≥ (# 3) ⌝ ≡ true
waits-add = refl , refl

interrupted : holds ⌜ ‵ heat · idle ≥ (# 2) · ‵ cool · idle ≥ (# 3) · ‵ log ⌝ ⌜ ‵ heat · idle ≥ (# 5) · ‵ log ⌝ ≡ false
interrupted = refl

------------------------------------------------------------------------
-- Activity is allowed only where a stretch allows it

not-nothing : holds {lower} ⌜ ‵ heat ⌝ ⌜ ε ⌝ ≡ false
not-nothing = refl

flanked : holds ⌜ ‵ heat ⌝ ⌜ ≥ (# 0) · ‵ heat · ≥ (# 0) ⌝ ≡ true
flanked = refl

-- a span covers an operation that takes at least its length
heat-covers : holds ⌜ ‵ heat ⌝ ⌜ ≥ (# 2) & ⁅ code heat ⁆ ⌝ ≡ true
heat-covers = refl

-- cooling takes more than one unit, so it covers "more than one"
cool-covers : holds ⌜ ‵ cool ⌝ ⌜ > (# 1) & ⁅ code cool ⁆ ⌝ ≡ true
cool-covers = refl

cool-short : holds ⌜ ‵ cool ⌝ ⌜ ≥ (3 / 2) & ⁅ code cool ⁆ ⌝ ≡ false
cool-short = refl

------------------------------------------------------------------------
-- Open and closed ends

open-below-closed : holds ⌜ idle > (# 1) ⌝ ⌜ idle ≥ (# 1) ⌝ ≡ true
open-below-closed = refl

closed-not-below-open : holds ⌜ idle ≥ (# 1) ⌝ ⌜ idle > (# 1) ⌝ ≡ false
closed-not-below-open = refl

-- distinct expressions with the same runs: the open wait before the
-- span can give it a little of its time
same-runs : holds ⌜ idle > (# 0) · (≥ (# 1) & ⁅ code log ⁆) ⌝ ⌜ idle > (# 0) · (> (# 1) & ⁅ code log ⁆) ⌝ ≡ true
          × holds ⌜ idle > (# 0) · (> (# 1) & ⁅ code log ⁆) ⌝ ⌜ idle > (# 0) · (≥ (# 1) & ⁅ code log ⁆) ⌝ ≡ true
same-runs = refl , refl

------------------------------------------------------------------------
-- The hull of a delay

delay-zero : holds (waitᴸ (# 0)) ⌜ ε ⌝ ≡ true × holds ⌜ ε ⌝ (waitᴸ (# 0)) ≡ true
delay-zero = refl , refl

delay-covers : holds (waitᴸ (1 / 2)) ⌜ idle ≥ (1 / 4) ⌝ ≡ true
delay-covers = refl

delay-short : holds (waitᴸ (1 / 4)) ⌜ idle > (1 / 4) ⌝ ≡ false
delay-short = refl

------------------------------------------------------------------------
-- An idle wait is made only from a span letter: `idle ‵ heat` is
-- refused

heat-not-span : span? (‵ heat) ≡ false
heat-not-span = refl
