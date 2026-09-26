------------------------------------------------------------------------
-- Worked instances of right-sided time paired with an energy budget.  --
--                                                                     --
-- The drifting-calibration grade `([0, n ] , [0, e ])`: orderings and  --
-- sequencing against a fixed budget, checked by the grade's own        --
-- decision procedure or by computation.                                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Product.RightSidedTimeEnergy where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)
open import Syntax.Grades.Example.Time.RightSided using ([0,_]; ↑_; ∞)
open import Syntax.Grades.Example.Product.RightSidedTimeEnergy
  using (right-sided-time×energy)

open import Util.Equality

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade right-sided-time×energy

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- a budget of 20 steps and 5 units

budget : Carrier
budget = ([0, ↑ 20 ] , [0, ↑ 5 ])

-- a send: up to 3 steps and 2 units

send : Carrier
send = ([0, ↑ 3 ] , [0, ↑ 2 ])

-- idling is free

idle : of-nat 7 ≡ ([0, ↑ 7 ] , [0, ↑ 0 ])
idle = refl

-- two sends and four idle steps fit the budget

two-sends : send · send · of-nat 4 ≡ ([0, ↑ 10 ] , [0, ↑ 4 ])
two-sends = refl

two-sends-fit : send · send · of-nat 4 ≾ budget
two-sends-fit = ≾! (send · send · of-nat 4) budget

-- three sends are fast enough but spend too much

three-sends-overspend : ¬ (send · send · send ≾ budget)
three-sends-overspend = ⋠! (send · send · send) budget

-- idling for 30 steps spends nothing but misses the deadline

long-idle-late : ¬ (of-nat 30 ≾ budget)
long-idle-late = ⋠! (of-nat 30) budget

-- the greatest grade: no deadline, no energy bound

top : ⊤ ≡ ([0, ∞ ] , [0, ∞ ])
top = refl
