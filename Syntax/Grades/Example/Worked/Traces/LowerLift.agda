------------------------------------------------------------------------
-- Worked instances of the trace-based interval grades.                --
--                                                                     --
-- The trace counterpart of `Worked.Time`, one submodule per       --
-- grade: `LeftSided` (a floor), `RightSided` (a cap), `TwoSided`       --
-- (both).                                                             --
--                                                                     --
-- Every claim is stated with the grade's own order `_≾_`, between two  --
-- sets of traces written out in full, in the form `unbox` reads it:    --
--                                                                     --
--     ρ' ≾ ρ    with  ρ' the effects that actually elapsed             --
--                and  ρ  the grade on the box being opened             --
--                                                                     --
-- so each line answers: does *this much having happened* open *that    --
-- box*? Each order is decidable, so `holds` and `fails` close the      --
-- claims by computation -- a claim asserted the wrong way round simply --
-- does not typecheck.                                                  --
--                                                                     --
-- The runs come from `Worked.Operations`:                              --
--                                                                     --
--   poll           read                                 1 tick        --
--   logged         read · write                         4 ticks       --
--   idle           ⟨ 2 ⟩                                2 ticks       --
--   uplink         read · ⟨ 2 ⟩ · send                  9 ticks       --
--   logged-uplink  read · write · ⟨ 2 ⟩ · send         12 ticks       --
--   chatty-uplink  read · ⟨ 2 ⟩ · send · send          15 ticks       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.LowerLift where

open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade; _→ᵍ_)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.SubtraceLift Op _≟ₒ_ cost
  using (≼ˢ-refl; _≼ˢ?_)

------------------------------------------------------------------------
-- A floor under what must have happened
--
-- `Grades.Example.Traces.LowerLift.LeftSided`, the trace counterpart of
-- `[ n ,+∞⟩`. The grade lists alternative demands, and a run discharges
-- it by doing at least what one of them asks for.

module LeftSided where

  open import Syntax.Grades.Example.Traces.LowerLift.LeftSided Op _≟ₒ_ cost
    using (lower-lift-left-sided; _≾_; _≾?_) public

  order : Grade._≾_ lower-lift-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Doing more than was demanded discharges the demand

  did-the-uplink-demanded-a-read : ⟅ uplink ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
  did-the-uplink-demanded-a-read = holds

  logged-on-the-way : ⟅ logged-uplink ⟆ ≾ ⟅ uplink ⟆
  logged-on-the-way = holds

  ----------------------------------------------------------------------
  -- Doing less does not

  did-a-poll-demanded-the-uplink : ¬ (⟅ poll ⟆ ≾ ⟅ uplink ⟆)
  did-a-poll-demanded-the-uplink = fails

  dropped-the-write : ¬ (⟅ uplink ⟆ ≾ ⟅ logged-uplink ⟆)
  dropped-the-write = fails

  ----------------------------------------------------------------------
  -- Elapsed time discharges a demand for time, operations included at
  -- their execution time: a read costs one tick, a write three

  read-covers-one-tick : ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 1 ⟩ ⟆
  read-covers-one-tick = holds

  read-covers-no-two : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 2 ⟩ ⟆)
  read-covers-no-two = fails

  write-covers-three-ticks : ⟅ ⌈ write ⌉ ⟆ ≾ ⟅ ⟨ 3 ⟩ ⟆
  write-covers-three-ticks = holds

  uplink-covers-nine-ticks : ⟅ uplink ⟆ ≾ ⟅ ⟨ 9 ⟩ ⟆
  uplink-covers-nine-ticks = holds

  uplink-covers-no-ten : ¬ (⟅ uplink ⟆ ≾ ⟅ ⟨ 10 ⟩ ⟆)
  uplink-covers-no-ten = fails

  ----------------------------------------------------------------------
  -- But nothing discharges a demand for an operation except that
  -- operation occurring, however long the run idles

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  idling-is-no-uplink : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ uplink ⟆)
  idling-is-no-uplink = fails

  ----------------------------------------------------------------------
  -- Alternatives, and the direction the floor is compared in.
  --
  -- The order asks that *every* demand of the weaker grade be covered
  -- by one of the stronger's -- the sets exchanged, exactly as
  -- `Inclusion.LeftSided`'s `Q ⊆ P`. So listing an extra demand on the
  -- right strengthens the grade rather than weakening it: the uplink
  -- covers the read but not twenty ticks of idling.

  not-both-of-those : ¬ (⟅ uplink ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  not-both-of-those = fails

  either-way-of-opening-it : ⟅ uplink ⟆ ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆
  either-way-of-opening-it = holds

  -- and listing an extra alternative on the *left* weakens it: the
  -- demand for an uplink is covered by the uplink among what was done,
  -- whether or not a mere poll was also possible

  polled-or-uplinked : ⟅ poll ∣ uplink ⟆ ≾ ⟅ uplink ⟆
  polled-or-uplinked = holds

  ----------------------------------------------------------------------
  -- The unit demands nothing, so it is the greatest grade -- as
  -- `[ 0 ,+∞⟩` is for the left-sided time intervals

  everything-opens-the-unit : ⟅ uplink ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆
  everything-opens-the-unit = holds {⟅ uplink ⟆} {⟅ ⟨ 0 ⟩ ⟆}

------------------------------------------------------------------------
-- A cap on what may have happened
--
-- `Grades.Example.Traces.LowerLift.RightSided`, the mirror image and
-- the trace counterpart of `[0, n ]`. The grade lists alternative
-- permissions, and a run stays within it by doing at most what one of
-- them allows.

module RightSided where

  open import Syntax.Grades.Example.Traces.LowerLift.RightSided Op _≟ₒ_ cost
    using (lower-lift-right-sided; _≾_; _≾?_) public

  order : Grade._≾_ lower-lift-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Doing less than the cap permits stays within it

  polled-under-an-uplink : ⟅ poll ⟆ ≾ ⟅ uplink ⟆
  polled-under-an-uplink = holds

  uplink-under-a-logged-uplink : ⟅ uplink ⟆ ≾ ⟅ logged-uplink ⟆
  uplink-under-a-logged-uplink = holds

  ----------------------------------------------------------------------
  -- Doing more does not

  transmitted-twice : ¬ (⟅ chatty-uplink ⟆ ≾ ⟅ uplink ⟆)
  transmitted-twice = fails

  ----------------------------------------------------------------------
  -- A cap naming an operation may be spent on idling instead, at that
  -- operation's execution time -- the mirror of the floor's "elapsed
  -- time discharges a demand for time"

  idled-within-a-read : ⟅ ⟨ 1 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆
  idled-within-a-read = holds

  idled-beyond-a-read : ¬ (⟅ ⟨ 2 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idled-beyond-a-read = fails

  ----------------------------------------------------------------------
  -- But a cap written as pure time permits no operations at all: the
  -- cap bounds behaviour, not merely consumption

  read-outside-a-tick : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 1 ⟩ ⟆)
  read-outside-a-tick = fails

  ----------------------------------------------------------------------
  -- The unit permits nothing but an instantaneous run, so it is the
  -- least grade -- as `[0, 0 ]` is for the right-sided time intervals

  nothing-fits-under-the-unit : ¬ (⟅ ⟨ 1 ⟩ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆)
  nothing-fits-under-the-unit = fails

  instant-does : ⟅ ⟨ 0 ⟩ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆
  instant-does = holds

------------------------------------------------------------------------
-- Both bounds at once
--
-- `Grades.Example.Traces.LowerLift.TwoSided`, the trace counterpart of
-- `[ min , max ]`. A grade is a pair of the two above, and its order is
-- their pair: the floor may drop and the cap may rise.

module TwoSided where

  open import Syntax.Grades.Example.Traces.LowerLift.TwoSided Op _≟ₒ_ cost
    using (TraceInterval; [_,_,_]; lo; hi; lower-lift-two-sided;
           _≾ᵗⁱ_; _≾ᵗⁱ?_; _·ᵗⁱ_; uᵗⁱ; eqᵗⁱ) public

  order : Grade._≾_ lower-lift-two-sided ≡ _≾ᵗⁱ_
  order = refl

  -- the order unfolds through the endpoint projections, so unlike the
  -- one-sided grades it does not determine the two intervals from the
  -- goal; they are named again here

  holds : (i j : TraceInterval) {p : True (i ≾ᵗⁱ? j)} → i ≾ᵗⁱ j
  holds i j {p} = toWitness p

  fails : (i j : TraceInterval) {p : False (i ≾ᵗⁱ? j)} → ¬ (i ≾ᵗⁱ j)
  fails i j {p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Writing intervals down
  --
  -- The third field is the analogue of `min≤max`: the floor must be
  -- achievable within the cap. For a singleton interval it is
  -- reflexivity; otherwise it is a right-sided ordering, settled by the
  -- same computation as the examples.

  -- exactly this run, no more and no less

  exactly : Trace → TraceInterval
  exactly t = [ ⟅ t ⟆ , ⟅ t ⟆ , ≼ˢ-refl {traces ⟅ t ⟆} ]

  -- at least a reading, at most a full uplink

  sensed : TraceInterval
  sensed =
    [ ⟅ ⌈ read ⌉ ⟆
    , ⟅ uplink ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≼ˢ? traces ⟅ uplink ⟆} tt
    ]

  -- at least one tick, at most a logged uplink: wider at both ends

  loose : TraceInterval
  loose =
    [ ⟅ ⟨ 1 ⟩ ⟆
    , ⟅ logged-uplink ⟆
    , toWitness {a? = traces ⟅ ⟨ 1 ⟩ ⟆ ≼ˢ? traces ⟅ logged-uplink ⟆} tt
    ]

  ----------------------------------------------------------------------
  -- Within both bounds: the uplink reads, and is itself the cap

  the-uplink : exactly uplink ≾ᵗⁱ sensed
  the-uplink = holds (exactly uplink) sensed

  ----------------------------------------------------------------------
  -- Under the floor: nothing has happened, so no reading was taken.
  -- Idling would not help either -- the floor names an operation.

  nothing-yet : ¬ (exactly ⟨ 0 ⟩ ≾ᵗⁱ sensed)
  nothing-yet = fails (exactly ⟨ 0 ⟩) sensed

  only-idled : ¬ (exactly idle ≾ᵗⁱ sensed)
  only-idled = fails (exactly idle) sensed

  ----------------------------------------------------------------------
  -- Over the cap: `chatty-uplink` reads, waits and sends -- and then
  -- sends again. It clears the floor comfortably, and the one-sided
  -- grade accepts it; the cap does not.

  transmitted-twice : ¬ (exactly chatty-uplink ≾ᵗⁱ sensed)
  transmitted-twice = fails (exactly chatty-uplink) sensed

  clears-the-floor : LeftSided._≾_ ⟅ chatty-uplink ⟆ ⟅ ⌈ read ⌉ ⟆
  clears-the-floor = LeftSided.holds

  breaks-the-cap : ¬ (RightSided._≾_ ⟅ chatty-uplink ⟆ ⟅ uplink ⟆)
  breaks-the-cap = RightSided.fails

  ----------------------------------------------------------------------
  -- Widening the interval weakens it, each endpoint outwards

  wider : sensed ≾ᵗⁱ loose
  wider = holds sensed loose

  narrower : ¬ (loose ≾ᵗⁱ sensed)
  narrower = fails loose sensed

  ----------------------------------------------------------------------
  -- The monoid and the unit
  --
  -- The product is the language product on each endpoint, and the unit
  -- is the singleton interval at the empty run: it demands nothing, but
  -- permits nothing either.

  sequencing : exactly poll ·ᵗⁱ exactly ⌈ write ⌉ ≡ exactly logged
  sequencing = eqᵗⁱ refl refl

  unit : Grade.u lower-lift-two-sided ≡ exactly ⟨ 0 ⟩
  unit = eqᵗⁱ refl refl

  two-time-steps : Grade.of-nat lower-lift-two-sided 2 ≡ exactly ⟨ 2 ⟩
  two-time-steps = eqᵗⁱ refl refl

  nothing-below-the-unit : ¬ (exactly uplink ≾ᵗⁱ uᵗⁱ)
  nothing-below-the-unit = fails (exactly uplink) uᵗⁱ

------------------------------------------------------------------------
-- Forgetting the cap
--
-- `System.TraceIntervalsToTraceSets` keeps the floor alone, the
-- trace-level counterpart of forgetting an interval's upper endpoint.
-- What it loses is exactly the row above that the cap rejected.

module ForgettingTheCap where

  open TwoSided using (sensed; exactly; the-uplink)

  open import Syntax.Grades.Example.Worked.Spec using (spec)
  open import Syntax.Grades.Example.System.TraceIntervalsToTraceSets spec
    using (trace-intervals→traces)

  open _→ᵍ_ using (map; map-monotone)

  reads-off-the-floor : map (trace-intervals→traces cost) sensed ≡ ⟅ ⌈ read ⌉ ⟆
  reads-off-the-floor = refl

  -- two boxes differing only in what they forbid become the same
  -- resource grade

  cap-forgotten :
      map (trace-intervals→traces cost) sensed
    ≡ map (trace-intervals→traces cost) (exactly ⌈ read ⌉)
  cap-forgotten = refl

  -- and monotonicity carries the interval ordering across

  projected : LeftSided._≾_ ⟅ uplink ⟆ ⟅ ⌈ read ⌉ ⟆
  projected =
    map-monotone (trace-intervals→traces cost)
                 {exactly uplink} {sensed} the-uplink
