------------------------------------------------------------------------
-- Worked instances of the two-sided trace intervals.                  --
--                                                                     --
-- A grade `[ L , U ]` bounds a run from both sides: it must cover some --
-- trace of the floor `L` and fit inside some trace of the cap `U`.     --
-- Read through `unbox`'s premise `ρ' ≾ᵣ ρ`, an elapsed grade discharges --
-- a demand when its floor is at least as demanding and its cap at most --
-- as permissive.                                                       --
--                                                                     --
-- The running demand is `sensed`: at least a reading must have been    --
-- taken, and nothing beyond a full uplink may have happened.           --
--                                                                     --
--                                       floor half   cap half   ≾      --
--   { uplink }   vs  sensed                yes         yes      yes   --
--   { ε }        vs  sensed                no          yes      no    --
--   { chatty }   vs  sensed                yes         no       no    --
--                                                                     --
-- Row 3 is what the whole grade exists for, and what neither           --
-- `TraceSet.UpToSubtrace` nor `TraceSet.Convex` can express: a run     --
-- that does *more* than demanded is rejected by the cap.               --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.TraceIntervals where

open import Data.List.Base using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here)
open import Data.Product using (_,_; proj₁; proj₂)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness; fromWitness)

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.Subtrace Op cost using (_≼_; ≼-refl)
open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost using (_≼ˢ_; _≽ˢ_)

open import Syntax.Grades.Example.TraceSet.UpToSubtrace Op _≟ₒ_ cost
  using () renaming (_≾_ to _≾ˢ_)

open import Syntax.Grades.Example.TraceSet.TwoSided Op _≟ₒ_ cost
  using (TraceInterval; [_,_,_]; lo; hi; _≾ᵗⁱ_; _·ᵗⁱ_; uᵗⁱ; eqᵗⁱ;
         two-sided-traces)

open import Syntax.Grades.Example.Worked.TraceSets
  using (_≼!_; _⋠!_; meets; achieves; mem; read-done)

------------------------------------------------------------------------
-- Building intervals
--
-- The consistency field `lo≼hi` is the analogue of `min≤max`, and like
-- the numeric side conditions in `Worked.Intervals` it is discharged by
-- running the decision procedure -- here on each trace of the floor.

-- a singleton interval: exactly this run, nothing more or less

exactly : (t : Trace) → TraceInterval
exactly t = [ set₁ t , set₁ t , achieves (λ { (here refl) → here (≼-refl t) }) ]

-- the demand the examples turn on: at least a reading, at most a full
-- uplink

sensed : TraceInterval
sensed =
  [ set₁ ⌈ read ⌉
  , set₁ uplink
  , achieves (λ { (here refl) → here read-done })
  ]

------------------------------------------------------------------------
-- Row 1: within both bounds
--
-- The uplink covers the floor (it takes a reading) and fits inside the
-- cap (it *is* the cap), so it discharges the demand.

within : exactly uplink ≾ᵗⁱ sensed
within = meets   (λ { (here refl) → here read-done })
       , achieves (λ { (here refl) → here (uplink ≼! uplink) })

------------------------------------------------------------------------
-- Row 2: under the floor
--
-- Nothing has happened yet. That is well inside the cap, but it does
-- not cover the floor: an empty run has no slack to pay for a read.
--
-- Note how little it takes to clear this floor -- `⟨ 1 ⟩` already does,
-- since a read costs one tick and time pays for operations. The empty
-- run is the only thing that does not.

nothing-yet : TraceInterval
nothing-yet = exactly ε

read-not-free : ¬ (⌈ read ⌉ ≼ ε)
read-not-free = ⌈ read ⌉ ⋠! ε

below-floor : ¬ (nothing-yet ≾ᵗⁱ sensed)
below-floor (l , _) = l ε (mem (set₁ ε) ε (here refl))

-- the cap half is untroubled: an empty run fits inside anything

within-cap : traces (hi nothing-yet) ≼ˢ traces (hi sensed)
within-cap = achieves (λ { (here refl) → here (ε ≼! uplink) })

-- one tick already clears the floor

one-tick-suffices : set₁ ⟨ 1 ⟩ ≾ˢ set₁ ⌈ read ⌉
one-tick-suffices = meets λ { (here refl) → here (⌈ read ⌉ ≼! ⟨ 1 ⟩) }

------------------------------------------------------------------------
-- Row 3: over the cap
--
-- `chatty` reads, waits, sends -- and then sends again. It covers the
-- floor comfortably, so `TraceSet.UpToSubtrace` accepts it. The cap
-- rejects it: a second transmission is not something the demand allows.

chatty : Trace
chatty = uplink ∙ ⌈ send ⌉

did-chatty : TraceInterval
did-chatty = exactly chatty

-- the floor half holds

chatty-covers-floor : set₁ chatty ≾ˢ set₁ ⌈ read ⌉
chatty-covers-floor = meets λ { (here refl) → here (⌈ read ⌉ ≼! chatty) }

-- the cap half does not

chatty-breaks-cap : ¬ (chatty ≼ uplink)
chatty-breaks-cap = chatty ⋠! uplink

over-cap : ¬ (did-chatty ≾ᵗⁱ sensed)
over-cap (_ , h) = h chatty (mem (set₁ chatty) chatty (here refl))

-- so the cap is exactly what the one-sided grade is missing: the same
-- pair is accepted there, and rejected here

one-sided-accepts : set₁ chatty ≾ˢ set₁ ⌈ read ⌉
one-sided-accepts = chatty-covers-floor

------------------------------------------------------------------------
-- The monoid and the unit
--
-- The product is the language product on each endpoint, so sequencing
-- two intervals sequences their floors and their caps.

seq-interval : exactly poll ·ᵗⁱ exactly ⌈ write ⌉ ≡ exactly logged
seq-interval = eqᵗⁱ refl refl

-- the unit is the singleton interval at the empty run, and `n` time
-- steps is the singleton interval at the pure delay -- exactly as
-- `of-nat n` is `[ n , n ]` for the two-sided time intervals

interval-unit : Grade.u two-sided-traces ≡ exactly ⟨ 0 ⟩
interval-unit = eqᵗⁱ refl refl

interval-of-nat : Grade.of-nat two-sided-traces 2 ≡ exactly ⟨ 2 ⟩
interval-of-nat = eqᵗⁱ refl refl

-- unlike the one-sided grade, the unit is *not* the greatest element:
-- it caps at the empty run, so nothing that takes time lies below it

not-below-unit : ¬ (exactly uplink ≾ᵗⁱ uᵗⁱ)
not-below-unit (_ , h) = h uplink (mem (set₁ uplink) uplink (here refl))

------------------------------------------------------------------------
-- The projection that forgets the cap
--
-- `System.TraceIntervalsToTraceSets` keeps the floor alone, which is
-- the trace-level counterpart of forgetting an interval's upper
-- endpoint. Row 3 is what that projection loses.

open import Syntax.Grades.Example.Worked.Spec using (spec)
open import Syntax.Grades.Example.System.TraceIntervalsToTraceSets spec
  using (trace-intervals→traces)

open _→ᵍ_ using (map; map-monotone)

forget-cap : map (trace-intervals→traces cost) sensed ≡ set₁ ⌈ read ⌉
forget-cap = refl

-- two demands differing only in what they forbid become the same
-- resource grade

cap-forgotten :
    map (trace-intervals→traces cost) sensed
  ≡ map (trace-intervals→traces cost) (exactly ⌈ read ⌉)
cap-forgotten = refl

-- and monotonicity carries row 1 across

within-projected : set₁ uplink ≾ˢ set₁ ⌈ read ⌉
within-projected =
  map-monotone (trace-intervals→traces cost)
               {exactly uplink} {sensed} within
