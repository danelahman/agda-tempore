------------------------------------------------------------------------
-- Worked instances of upper bounds on time paired with an energy     --
-- budget.                                                            --
--                                                                    --
-- The drifting-calibration grade `([0, n ] , [0, e ])` at the sensor --
-- node, each operation graded by `slow` and `draws`: orderings and   --
-- sequencing against a fixed budget, established by the decision     --
-- procedure of the grade or by computation.                          --
------------------------------------------------------------------------

module Grades.Examples.Worked.Product.TimeUpperBoundEnergy where

open import Data.Product using (_,_)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Grades.Base using (Grade)
open import Grades.Examples.Time.UpperBound using ([0,_]; ↑_; ∞)
open import Grades.Examples.Product.TimeUpperBoundEnergy
  using (time-upper-bound×energy)

open import Grades.Examples.Worked.Operations
  using (Op; read; send; slow)
open import Grades.Examples.Worked.Operations.Footprint using (draws)

open import Util.Equality

------------------------------------------------------------------------
-- Checked orderings, by the grade's decision procedure

open Grade time-upper-bound×energy

≾! : (c d : Carrier) {p : True (c ≾? d)} → c ≾ d
≾! _ _ {p} = toWitness p

⋠! : (c d : Carrier) {p : False (c ≾? d)} → ¬ (c ≾ d)
⋠! _ _ {p} = toWitnessFalse p

-- an operation of the sensor node: the time it may take at worst, and
-- the energy it draws

node : Op → Carrier
node o = ([0, ↑ slow o ] , [0, ↑ draws o ])

-- the `uplink` run: read, idle two ticks, send

uplink : Carrier
uplink = node read · ι 2 · node send

-- a budget of 30 steps and 12 units

budget : Carrier
budget = ([0, ↑ 30 ] , [0, ↑ 12 ])

-- idling is free

idle : ι 7 ≡ ([0, ↑ 7 ] , [0, ↑ 0 ])
idle = refl

-- an uplink takes nine steps at worst and draws six units

one-uplink : uplink ≡ ([0, ↑ 9 ] , [0, ↑ 6 ])
one-uplink = refl

-- two uplinks fit the budget

two-uplinks-fit : uplink · uplink ≾ budget
two-uplinks-fit = ≾! (uplink · uplink) budget

-- three are fast enough, taking 27 steps, but draw 18 units

three-uplinks-overdraw : ¬ (uplink · uplink · uplink ≾ budget)
three-uplinks-overdraw = ⋠! (uplink · uplink · uplink) budget

-- idling for 31 steps draws nothing but misses the deadline

long-idle-late : ¬ (ι 31 ≾ budget)
long-idle-late = ⋠! (ι 31) budget

-- the greatest grade: no deadline, no energy bound

top : ⊤ ≡ ([0, ∞ ] , [0, ∞ ])
top = refl
