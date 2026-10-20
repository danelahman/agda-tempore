------------------------------------------------------------------------
-- Worked rigid timed regular-expression lower bounds in dense time.  --
--                                                                    --
-- The operations of `Rigid.Finite.Operations`. The cases: waits add  --
-- up under iteration; the empty word is no wait; activity needs      --
-- explicit flanks, here iterated; open against closed ends under     --
-- iteration; the Kleene plus; and the hull of a delay.               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Rigid.Rational.LeftSided where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Subset using (⁅_⁆)
open import Data.Product using (_×_; _,_)

open import Util.Equality

open import Syntax.Grades.Example.Time.Dense.TwoSided using (_/_; #_)
open import Syntax.Grades.Example.Worked.Traces.Rigid.Finite.Operations
open import Syntax.Grades.Example.Traces.Rigid.Rational.LeftSided Op 3 code name name-code code-name running

L : OpSet
L = ⁅ code log ⁆

------------------------------------------------------------------------
-- Waits add up under iteration; iterating admits the empty word

waits-iterated : holds ⌜ !≥ (# 1) · !≥ (# 1) ⌝ ⌜ (!≥ (# 1)) * ⌝ ≡ true
               × holds ⌜ (!≥ (# 1)) * ⌝ ⌜ !≥ (# 1) ⌝ ≡ false
waits-iterated = refl , refl

-- at least one wait of at least a unit is a wait of at least a unit
waits-plus : holds (⌜ !≥ (# 1) ⌝ ⁺ᵉ) ⌜ !≥ (# 1) ⌝ ≡ true
           × holds ⌜ !≥ (# 1) ⌝ (⌜ !≥ (# 1) ⌝ ⁺ᵉ) ≡ true
waits-plus = refl , refl

------------------------------------------------------------------------
-- Logs, iterated, within a stretch admitting them; an interrupting
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

delay-iterated : holds (waitᴸ (# 2)) ⌜ (!≥ (1 / 2)) * ⌝ ≡ true
delay-iterated = refl
