------------------------------------------------------------------------
-- Worked instances of the trace-based interval grades.                --
--                                                                     --
-- The trace counterpart of `Worked.Time`, one submodule per grade:    --
-- `LeftSided` (a floor), `RightSided` (a cap), `TwoSided` (both).      --
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
-- The runs are written out in full in every claim rather than through  --
-- the shorthands of `Worked.Operations`, so that a claim can be read   --
-- without looking anything up. Their durations under `cost` -- read 1, --
-- write 3, send 6 -- are:                                              --
--                                                                     --
--   ⌈ read ⌉                                          1 tick          --
--   ⌈ read ⌉ ∙ ⌈ write ⌉                              4 ticks         --
--   ⟨ 2 ⟩                                             2 ticks         --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉                       9 ticks         --
--   ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉          12 ticks         --
--   ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉           15 ticks         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subtrace.LowerLift where

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
-- `Grades.Example.Traces.Subtrace.LowerLift.LeftSided`, the trace counterpart of
-- `[ n ,+∞⟩`. The grade lists alternative demands, and a run discharges
-- it by doing at least what one of them asks for.

module LeftSided where

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.LeftSided Op _≟ₒ_ cost
    using (lower-lift-left-sided; _≾_; _≾?_) public

  order : Grade._≾_ lower-lift-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Doing more than was demanded discharges the demand

  did-the-uplink-demanded-a-read : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                                   ≾ ⟅ ⌈ read ⌉ ⟆
  did-the-uplink-demanded-a-read = holds

  logged-on-the-way : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-on-the-way = holds

  ----------------------------------------------------------------------
  -- Doing less does not

  did-a-poll-demanded-the-uplink : ¬ (⟅ ⌈ read ⌉ ⟆
                                     ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  did-a-poll-demanded-the-uplink = fails

  dropped-the-write : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                        ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
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

  uplink-covers-nine-ticks : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 9 ⟩ ⟆
  uplink-covers-nine-ticks = holds

  uplink-covers-no-ten : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 10 ⟩ ⟆)
  uplink-covers-no-ten = fails

  ----------------------------------------------------------------------
  -- But nothing discharges a demand for an operation except that
  -- operation occurring, however long the run idles

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  idling-is-no-uplink : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  idling-is-no-uplink = fails

  ----------------------------------------------------------------------
  -- Alternatives, and the direction the floor is compared in.
  --
  -- The order asks that *every* demand of the weaker grade be covered
  -- by one of the stronger's -- the sets exchanged, exactly as
  -- `Inclusion.LeftSided`'s `Q ⊆ P`. So listing an extra demand on the
  -- right strengthens the grade rather than weakening it: the uplink
  -- covers the read but not twenty ticks of idling.

  not-both-of-those : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                        ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  not-both-of-those = fails

  either-way-of-opening-it : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                             ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 9 ⟩ ⟆
  either-way-of-opening-it = holds

  -- and listing an extra alternative on the *left* weakens it: the
  -- demand for an uplink is covered by the uplink among what was done,
  -- whether or not a mere poll was also possible

  polled-or-uplinked : ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                       ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  polled-or-uplinked = holds

  ----------------------------------------------------------------------
  -- The unit demands nothing, so it is the greatest grade -- as
  -- `[ 0 ,+∞⟩` is for the left-sided time intervals

  everything-opens-the-unit : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆
  everything-opens-the-unit = holds {⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} {⟅ ⟨ 0 ⟩ ⟆}

------------------------------------------------------------------------
-- A cap on what may have happened
--
-- `Grades.Example.Traces.Subtrace.LowerLift.RightSided`, the mirror image and
-- the trace counterpart of `[0, n ]`. The grade lists alternative
-- permissions, and a run stays within it by doing at most what one of
-- them allows.

module RightSided where

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.RightSided Op _≟ₒ_ cost
    using (lower-lift-right-sided; _≾_; _≾?_) public

  order : Grade._≾_ lower-lift-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Doing less than the cap permits stays within it

  polled-under-an-uplink : ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  polled-under-an-uplink = holds

  uplink-under-a-logged-uplink : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                                 ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  uplink-under-a-logged-uplink = holds

  ----------------------------------------------------------------------
  -- Doing more does not

  transmitted-twice : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
                        ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
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

  ----------------------------------------------------------------------
  -- Alternatives. The cap quantifies over the *elapsed* set and finds
  -- its witness in the demanded one, so every run offered must fit
  -- inside some permitted one -- and a single permission may serve
  -- several offered runs at once.

  both-under-one-cap : ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
                     ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  both-under-one-cap = holds

  -- one run over the cap breaks it, however well the others fit

  one-run-over-the-cap :
    ¬ (⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆
      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  one-run-over-the-cap = fails

  -- adding a permission is a weakening: the offered run picks whichever
  -- of them it fits inside

  picks-a-permission : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                     ≾ ⟅ ⌈ read ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  picks-a-permission = holds

  -- which is the direction the *floor* refuses: `LowerLift.LeftSided`
  -- would ask every listed alternative to be covered instead

------------------------------------------------------------------------
-- Both bounds at once
--
-- `Grades.Example.Traces.Subtrace.LowerLift.TwoSided`, the trace counterpart of
-- `[ min , max ]`. A grade is a pair of the two above, and its order is
-- their pair: the floor may drop and the cap may rise.

module TwoSided where

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.TwoSided Op _≟ₒ_ cost
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
    , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
    ]

  -- at least one tick, at most a logged uplink: wider at both ends

  loose : TraceInterval
  loose =
    [ ⟅ ⟨ 1 ⟩ ⟆
    , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , toWitness {a? = traces ⟅ ⟨ 1 ⟩ ⟆ ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
    ]

  -- an interval listing alternatives at *both* endpoints: at least a
  -- read or a tick, at most a store-and-stop or a full uplink

  branching : TraceInterval
  branching =
    [ ⟅ ⌈ read ⌉ ∣ ⟨ 1 ⟩ ⟆
    , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , toWitness
        {a? = traces ⟅ ⌈ read ⌉ ∣ ⟨ 1 ⟩ ⟆
           ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉
                      ∣ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
    ]

  ----------------------------------------------------------------------
  -- What alternatives buy at each endpoint, and what they do not.
  --
  -- The two endpoints quantify over opposite sets, so listing an extra
  -- alternative *strengthens* the floor and *weakens* the cap. An
  -- interval that branches is therefore not comparable with one that
  -- does not just because its endpoints look wider.

  -- the singleton uplink sits inside `branching`: it clears the read on
  -- the floor and fits the uplink on the cap

  uplink-in-branching : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≾ᵗⁱ branching
  uplink-in-branching =
    holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) branching

  -- but `branching` is *not* below `sensed`, though `sensed`'s endpoints
  -- are each one of `branching`'s: the extra floor alternative `⟨ 1 ⟩` is
  -- a demand `sensed`'s floor does not make, and the floor compares its
  -- sets exchanged, so it must be covered too

  branching-not-below-sensed : ¬ (branching ≾ᵗⁱ sensed)
  branching-not-below-sensed = fails branching sensed

  -- the other way round does hold: dropping the extra floor alternative
  -- and keeping only the larger cap is a weakening in both endpoints

  sensed-below-branching : sensed ≾ᵗⁱ branching
  sensed-below-branching = holds sensed branching

  ----------------------------------------------------------------------
  -- Within both bounds: the uplink reads, and is itself the cap

  the-uplink : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≾ᵗⁱ sensed
  the-uplink = holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) sensed

  ----------------------------------------------------------------------
  -- Under the floor: nothing has happened, so no reading was taken.
  -- Idling would not help either -- the floor names an operation.

  nothing-yet : ¬ (exactly ⟨ 0 ⟩ ≾ᵗⁱ sensed)
  nothing-yet = fails (exactly ⟨ 0 ⟩) sensed

  only-idled : ¬ (exactly ⟨ 2 ⟩ ≾ᵗⁱ sensed)
  only-idled = fails (exactly ⟨ 2 ⟩) sensed

  ----------------------------------------------------------------------
  -- Over the cap: `chatty-uplink` reads, waits and sends -- and then
  -- sends again. It clears the floor comfortably, and the one-sided
  -- grade accepts it; the cap does not.

  transmitted-twice : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉)
                        ≾ᵗⁱ sensed)
  transmitted-twice = fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉)) sensed

  clears-the-floor : LeftSided._≾_ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ⟅ ⌈ read ⌉ ⟆
  clears-the-floor = LeftSided.holds

  breaks-the-cap : ¬ (RightSided._≾_ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ∙ ⌈ send ⌉ ⟆ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
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

  sequencing : exactly ⌈ read ⌉ ·ᵗⁱ exactly ⌈ write ⌉ ≡ exactly (⌈ read ⌉ ∙ ⌈ write ⌉)
  sequencing = eqᵗⁱ refl refl

  unit : Grade.u lower-lift-two-sided ≡ exactly ⟨ 0 ⟩
  unit = eqᵗⁱ refl refl

  two-time-steps : Grade.of-nat lower-lift-two-sided 2 ≡ exactly ⟨ 2 ⟩
  two-time-steps = eqᵗⁱ refl refl

  nothing-below-the-unit : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉) ≾ᵗⁱ uᵗⁱ)
  nothing-below-the-unit = fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) uᵗⁱ

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

  projected : LeftSided._≾_ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ⟅ ⌈ read ⌉ ⟆
  projected =
    map-monotone (trace-intervals→traces cost)
                 {exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)} {sensed} the-uplink

