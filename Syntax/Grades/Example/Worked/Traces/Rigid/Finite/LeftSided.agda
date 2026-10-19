------------------------------------------------------------------------
-- Worked rigid timed finite-expression lower bounds in dense time.   --
--                                                                    --
-- The operations of `Operations`. The cases: strict waits add up,    --
-- undisturbed waits are kept, activity needs explicit flanks, open    --
-- against closed ends, an equivalence of distinct expressions, and   --
-- the hull of a delay.                                               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Finite.LeftSided where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Product using (_×_; _,_)

open import Util.Equality

open import Syntax.Grades.Example.Time.Dense.TwoSided using (_/_; #_)
open import Syntax.Grades.Example.Worked.Traces.Rigid.Finite.Operations
open import Syntax.Grades.Example.Traces.Rigid.Finite.LeftSided Op 3 code name name-code code-name running

------------------------------------------------------------------------
-- Strict waits add up, and undisturbed waits are kept

waits-add : holds ⌜ !≥ (# 2) · !≥ (# 3) ⌝ ⌜ !≥ (# 5) ⌝ ≡ true
          × holds ⌜ !≥ (# 5) ⌝ ⌜ !≥ (# 2) · !≥ (# 3) ⌝ ≡ true
waits-add = refl , refl

interrupted : holds ⌜ ‵ heat · !≥ (# 2) · ‵ cool · !≥ (# 3) · ‵ log ⌝ ⌜ ‵ heat · !≥ (# 5) · ‵ log ⌝ ≡ false
interrupted = refl

------------------------------------------------------------------------
-- Activity is allowed only where a stretch allows it

not-nothing : holds {lower} ⌜ ‵ heat ⌝ ⌜ ε ⌝ ≡ false
not-nothing = refl

flanked : holds ⌜ ‵ heat ⌝ ⌜ ≥ (# 0) · ‵ heat · ≥ (# 0) ⌝ ≡ true
flanked = refl

-- a budget covers an operation that takes at least its length
heat-covers : holds ⌜ ‵ heat ⌝ ⌜ ≥ (# 2) & ⁅ code heat ⁆ ⌝ ≡ true
heat-covers = refl

-- cooling takes more than one unit, so it covers "more than one"
cool-covers : holds ⌜ ‵ cool ⌝ ⌜ > (# 1) & ⁅ code cool ⁆ ⌝ ≡ true
cool-covers = refl

cool-short : holds ⌜ ‵ cool ⌝ ⌜ ≥ (3 / 2) & ⁅ code cool ⁆ ⌝ ≡ false
cool-short = refl

------------------------------------------------------------------------
-- Open and closed ends

open-below-closed : holds ⌜ !> (# 1) ⌝ ⌜ !≥ (# 1) ⌝ ≡ true
open-below-closed = refl

closed-not-below-open : holds ⌜ !≥ (# 1) ⌝ ⌜ !> (# 1) ⌝ ≡ false
closed-not-below-open = refl

-- distinct expressions with the same runs: the open wait before the
-- budget can give it a little of its time
same-runs : holds ⌜ !> (# 0) · (≥ (# 1) & ⁅ code log ⁆) ⌝ ⌜ !> (# 0) · (> (# 1) & ⁅ code log ⁆) ⌝ ≡ true
          × holds ⌜ !> (# 0) · (> (# 1) & ⁅ code log ⁆) ⌝ ⌜ !> (# 0) · (≥ (# 1) & ⁅ code log ⁆) ⌝ ≡ true
same-runs = refl , refl

------------------------------------------------------------------------
-- The hull of a delay

delay-zero : holds (waitᴸ (# 0)) ⌜ ε ⌝ ≡ true × holds ⌜ ε ⌝ (waitᴸ (# 0)) ≡ true
delay-zero = refl , refl

delay-covers : holds (waitᴸ (1 / 2)) ⌜ !≥ (1 / 4) ⌝ ≡ true
delay-covers = refl

delay-short : holds (waitᴸ (1 / 4)) ⌜ !> (1 / 4) ⌝ ≡ false
delay-short = refl
