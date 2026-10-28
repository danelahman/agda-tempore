------------------------------------------------------------------------
-- Worked rigid timed regular-expression upper bounds in dense time.  --
--                                                                    --
-- The operations of `Rigid.Finite.Operations`: heating takes two to  --
-- four units, cooling more than one and less than two, logging more  --
-- than a quarter and at most a half. The cases: open bounds add up,  --
-- so no grid of fixed resolution decides the order; an unbounded     --
-- stretch below an iteration of bounded ones, though below no single --
-- word of it; iteration against open ends; the window rule under     --
-- iteration; the Kleene plus; and the hull of a delay. Each          --
-- comparison is checked by evaluating the decision.                  --
------------------------------------------------------------------------

module Grades.Examples.Worked.Traces.Rigid.Rational.RightSided where

open import Data.Bool.Base using (true; false)
open import Data.Fin.Subset using (⁅_⁆; _∪_)
open import Data.Product using (_×_; _,_)

open import Util.Equality

open import Grades.Examples.Time.Dense.TwoSided using (_/_; #_)
open import Grades.Examples.Worked.Traces.Rigid.Finite.Operations
open import Grades.Examples.Traces.Rigid.Rational.RightSided Op 3 code name name-code code-name running

L C : OpSet
L = ⁅ code log ⁆
C = ⁅ code cool ⁆ ∪ ⁅ code log ⁆

------------------------------------------------------------------------
-- Open bounds add up: a wait of less than one, then logging time of
-- less than one, may total more than one, though on the grid of
-- halves every instance totals at most one

open-sum : holds ⌜ idle < (# 1) · (< (# 1) & L) ⌝ ⌜ ≤ (# 1) & L ⌝ ≡ false
open-sum = refl

open-sum-two : holds ⌜ idle < (# 1) · (< (# 1) & L) ⌝ ⌜ < (# 2) & L ⌝ ≡ true
open-sum-two = refl

------------------------------------------------------------------------
-- An unbounded stretch is an iteration of bounded ones

unbounded-iterated : holds ⌜ ≤∞ & C ⌝ ⌜ (< (# 2) & C) * ⌝ ≡ true
                   × holds ⌜ (< (# 2) & C) * ⌝ ⌜ ≤∞ & C ⌝ ≡ true
unbounded-iterated = refl , refl

-- iterated logging is a stretch admitting it, not conversely
logs-in-stretch : holds ⌜ ‵ log * ⌝ ⌜ ≤∞ & L ⌝ ≡ true
                × holds ⌜ ≤∞ & L ⌝ ⌜ ‵ log * ⌝ ≡ false
logs-in-stretch = refl , refl

------------------------------------------------------------------------
-- Iteration against open ends: one log of half a unit does not fit
-- less than half a unit, but spreads over two such stretches

log-open : holds ⌜ ‵ log ⌝ ⌜ < (1 / 2) & L ⌝ ≡ false
log-open = refl

log-open-iterated : holds ⌜ ‵ log * ⌝ ⌜ (< (1 / 2) & L) * ⌝ ≡ true
log-open-iterated = refl

------------------------------------------------------------------------
-- The window rule: a log spans stretches that all admit it, but not an
-- operation between them

log-across : holds ⌜ ‵ log ⌝ ⌜ (≤ (1 / 4) & L) * ⌝ ≡ true
log-across = refl

log-blocked : holds ⌜ ‵ log ⌝ ⌜ ((≤ (1 / 4) & L) · ‵ heat) * · (≤ (1 / 4) & L) ⌝ ≡ false
log-blocked = refl

------------------------------------------------------------------------
-- The Kleene plus: at least one log, each within half a unit

logs-plus : holds (⌜ ‵ log ⌝ ⁺ᵉ) ⌜ (≤ (1 / 2) & L) · (≤ (1 / 2) & L) * ⌝ ≡ true
          × holds {upper} ⌜ ε ⌝ (⌜ ‵ log ⌝ ⁺ᵉ) ≡ false
logs-plus = refl , refl

------------------------------------------------------------------------
-- The hull of a delay

delay-within : holds (waitᵁ (3 / 2)) ⌜ (idle ≤ (1 / 2)) * ⌝ ≡ true
delay-within = refl
