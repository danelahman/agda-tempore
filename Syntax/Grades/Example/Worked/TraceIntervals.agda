------------------------------------------------------------------------
-- Worked instances of the two-sided trace intervals.                  --
--                                                                     --
-- As in `Worked.TraceSets`, every claim is stated with the grade order --
-- `_≾_` in the form `unbox` reads it, `ρ' ≾ ρ` with `ρ'` elapsed and   --
-- `ρ` the grade on the box.                                           --
--                                                                     --
-- A grade `[ L , U ]` bounds a run from both sides, its two halves     --
-- being exactly the two one-sided grades: the floor `L` is ordered as  --
-- in `TraceSet.LeftSided` and the cap `U` as in `TraceSet.RightSided`. --
--                                                                     --
-- The running demand is `sensed`: at least a reading must have been    --
-- taken, and nothing beyond a full uplink may have happened.           --
--                                                                     --
--                                       floor   cap    ≾               --
--   exactly uplink  vs  sensed           yes    yes   yes             --
--   exactly ε       vs  sensed           no     yes   no              --
--   exactly chatty  vs  sensed           yes    no    no              --
--                                                                     --
-- The last row is what the interval exists for, and what no order on a --
-- single set of traces can reject.                                     --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.TraceIntervals where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.Subtrace Op cost
  using (_≼_; ≼-refl; module DecSubtrace)
open DecSubtrace _≟ₒ_ using (_≼?_)
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost using (_≼ˢ_; _≽ˢ_)

open import Syntax.Grades.Example.TraceSet.LeftSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ˡᵒ_)
open import Syntax.Grades.Example.TraceSet.RightSided Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ʰⁱ_)

open import Syntax.Grades.Example.TraceSet.TwoSided Op _≟ₒ_ cost
  using (TraceInterval; [_,_,_]; lo; hi; _≾ᵗⁱ_; _·ᵗⁱ_; uᵗⁱ; eqᵗⁱ;
         two-sided-traces)

open import Syntax.Grades.Example.Worked.TraceSets
  using (mem; module LeftSided; module RightSided)

module LS = LeftSided
module RS = RightSided

open LS using () renaming (_≾!_ to _≾ˡᵒ!_; meets to floor-of)
open RS using () renaming (_≾!_ to _≾ʰⁱ!_; permits to cap-of)

------------------------------------------------------------------------
-- Building intervals
--
-- The consistency field `lo≼hi` is the analogue of `min≤max`: the floor
-- must be achievable within the cap. Like the numeric side conditions
-- in `Worked.Intervals`, it is discharged by running the decision
-- procedure.

-- a singleton interval: exactly this run, no more and no less

exactly : (t : Trace) → TraceInterval
exactly t = [ set₁ t , set₁ t , cap-of {set₁ t} {set₁ t}
                                  (λ { (here refl) → here (≼-refl t) }) ]

-- the demand the examples turn on: at least a reading, at most a full
-- uplink

sensed : TraceInterval
sensed =
  [ set₁ ⌈ read ⌉
  , set₁ uplink
  , cap-of {set₁ ⌈ read ⌉} {set₁ uplink}
      (λ { (here refl) → here (toWitness {a? = ⌈ read ⌉ ≼? uplink} tt) })
  ]

------------------------------------------------------------------------
-- Row 1: within both bounds
--
-- The uplink covers the floor (it takes a reading) and stays within the
-- cap (it *is* the cap), so it opens the box.

within : exactly uplink ≾ᵗⁱ sensed
within = (uplink ≾ˡᵒ! ⌈ read ⌉) , (uplink ≾ʰⁱ! uplink)

------------------------------------------------------------------------
-- Row 2: under the floor
--
-- Nothing has happened yet. That is well within the cap, but it does
-- not cover the floor: an empty run performs no read.
--
-- Nor would idling for any length of time, however long: the floor
-- names an *operation*, and elapsed time never buys one. Only a floor
-- phrased as elapsed time is dischargeable by waiting.

nothing-yet : TraceInterval
nothing-yet = exactly ε

below-floor : ¬ (nothing-yet ≾ᵗⁱ sensed)
below-floor (l , _) = LS._⋠!_ ε ⌈ read ⌉ l

within-cap : hi nothing-yet ≾ʰⁱ hi sensed
within-cap = ε ≾ʰⁱ! uplink

waiting-misses-floor : ¬ (set₁ ⟨ 100 ⟩ ≾ˡᵒ set₁ ⌈ read ⌉)
waiting-misses-floor = LS._⋠!_ ⟨ 100 ⟩ ⌈ read ⌉

-- whereas a floor asking only for time is discharged by the read, which
-- costs a tick

read-clears-a-tick : set₁ ⌈ read ⌉ ≾ˡᵒ set₁ ⟨ 1 ⟩
read-clears-a-tick = ⌈ read ⌉ ≾ˡᵒ! ⟨ 1 ⟩


------------------------------------------------------------------------
-- Row 3: over the cap
--
-- `chatty` reads, waits, sends -- and then sends again. It covers the
-- floor comfortably, so the one-sided grade accepts it. The cap does
-- not: a second transmission is not something the box allows.

chatty : Trace
chatty = uplink ∙ ⌈ send ⌉

did-chatty : TraceInterval
did-chatty = exactly chatty

covers-floor : lo did-chatty ≾ˡᵒ lo sensed
covers-floor = chatty ≾ˡᵒ! ⌈ read ⌉

breaks-cap : ¬ (hi did-chatty ≾ʰⁱ hi sensed)
breaks-cap = RS._⋠!_ chatty uplink

over-cap : ¬ (did-chatty ≾ᵗⁱ sensed)
over-cap (_ , h) = breaks-cap h

------------------------------------------------------------------------
-- The monoid and the unit

seq-interval : exactly poll ·ᵗⁱ exactly ⌈ write ⌉ ≡ exactly logged
seq-interval = eqᵗⁱ refl refl

interval-unit : Grade.u two-sided-traces ≡ exactly ⟨ 0 ⟩
interval-unit = eqᵗⁱ refl refl

interval-of-nat : Grade.of-nat two-sided-traces 2 ≡ exactly ⟨ 2 ⟩
interval-of-nat = eqᵗⁱ refl refl

-- the unit is neither greatest nor least: its floor demands nothing but
-- its cap permits nothing, so only an instantaneous run lies below it

not-below-unit : ¬ (exactly uplink ≾ᵗⁱ uᵗⁱ)
not-below-unit (_ , h) = RS._⋠!_ uplink ε h

------------------------------------------------------------------------
-- The projection that forgets the cap
--
-- `System.TraceIntervalsToTraceSets` keeps the floor alone, the
-- trace-level counterpart of forgetting an interval's upper endpoint.
-- Row 3 is what that projection loses.

open import Syntax.Grades.Example.Worked.Spec using (spec)
open import Syntax.Grades.Example.System.TraceIntervalsToTraceSets spec
  using (trace-intervals→traces)

open _→ᵍ_ using (map; map-monotone)

forget-cap : map (trace-intervals→traces cost) sensed ≡ set₁ ⌈ read ⌉
forget-cap = refl

-- two boxes differing only in what they forbid become the same resource
-- grade

cap-forgotten :
    map (trace-intervals→traces cost) sensed
  ≡ map (trace-intervals→traces cost) (exactly ⌈ read ⌉)
cap-forgotten = refl

-- and monotonicity carries row 1 across

within-projected : set₁ uplink ≾ˡᵒ set₁ ⌈ read ⌉
within-projected =
  map-monotone (trace-intervals→traces cost)
               {exactly uplink} {sensed} within
