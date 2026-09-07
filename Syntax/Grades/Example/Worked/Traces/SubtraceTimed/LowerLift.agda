------------------------------------------------------------------------
-- Worked instances of the lower-lift column over the time-strict      --
-- sub-trace order.                                                    --
--                                                                     --
-- `Grades.Example.Traces.SubtraceTimed.LowerLift`, laid out as the     --
-- lenient column in `Worked.Traces.Subtrace.LowerLift` is:             --
-- `LeftSided` (a floor), `RightSided` (a cap), `TwoSided` (both).      --
--                                                                     --
-- What changes is *where* a run may spend the time a demand asks for.  --
-- A matched operation divides both traces into windows, and a delay    --
-- the demand places in one window must be covered by what the run      --
-- does in the same one. Time is no longer banked across the whole run. --
--                                                                     --
-- Wherever the two orders part company the claim is stated against     --
-- both, so the separation is decided from both sides rather than       --
-- asserted. Under `cost` -- read 1, write 3, send 6 -- the three runs  --
-- the examples turn on all take ten ticks and differ only in where the --
-- write falls:                                                        --
--                                                                     --
--   ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉    between the read and the send  --
--   ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉    before the read                --
--   ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉    after the send                 --
--                                                                     --
-- against the demand `⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉`, which asks for two --
-- ticks between the two operations it names.                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.SubtraceTimed.LowerLift where

open import Data.Product using (_,_)
open import Data.Unit using (tt)

open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable
  using (True; False; toWitness; toWitnessFalse)

open import Syntax.Grades using (Grade)

open import Util.Equality

open import Syntax.Grades.Example.Worked.Operations

open import Syntax.Grades.Traces.SubtraceTimedLift Op _≟ₒ_ cost
  using (_≼ˢ_; ≼ˢ-refl; _≼ˢ?_)

------------------------------------------------------------------------
-- A floor under what must have happened
--
-- `SubtraceTimed.LowerLift.LeftSided`. The grade lists alternative
-- demands, and a run discharges it by doing at least what one of them
-- asks for -- now with each demanded delay paid for in its own window.

module LeftSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.LeftSided
    Op _≟ₒ_ cost using (lower-lift-left-sided; _≾_; _≾?_) public

  -- the same grade over the lenient order, to state the separations
  -- against; the carrier is the same, so both orders compare the same
  -- pairs of sets

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.LeftSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵉⁿ_; _≾?_ to _≾ˡᵉⁿ?_)

  order : Grade._≾_ lower-lift-left-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsˡᵉⁿ : {P Q : NeTraces} {p : True (P ≾ˡᵉⁿ? Q)} → P ≾ˡᵉⁿ Q
  holdsˡᵉⁿ {p = p} = toWitness p

  failsˡᵉⁿ : {P Q : NeTraces} {p : False (P ≾ˡᵉⁿ? Q)} → ¬ (P ≾ˡᵉⁿ Q)
  failsˡᵉⁿ {p = p} = toWitnessFalse p

  ----------------------------------------------------------------------
  -- Unmatched operations in the middle are still tolerated
  --
  -- The run does everything the demand asks for and logs on the way,
  -- and the demand is still discharged. This order restricts *when* a
  -- run may spend time, not which operations it may interleave: the
  -- match is still a subsequence match.
  --
  -- Contiguity is not available to restrict instead. `Traces.Prefix`
  -- exhibits the failure of `·-monoˡ-≾` for the prefix order, and the
  -- same argument covers any order asking the demanded events to be
  -- adjacent -- so tolerating a write on the way is what makes these
  -- grades monoid-graded, not a looseness left over.

  logged-on-the-way : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-on-the-way = holds

  logged-on-the-way-leniently : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                                ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-on-the-way-leniently = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- The separation, at the grade level
  --
  -- The demand asks for a read, then two ticks, then a send. A write
  -- takes three ticks, so wherever it falls there is time enough; the
  -- question is whether it falls where the demand puts it. Dropping the
  -- delay the run idles for, so that the write has to cover the two
  -- ticks by itself, is what brings that question into view.

  -- between the two: accepted by both orders

  logged-in-the-window : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                         ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-in-the-window = holds

  logged-in-the-window-leniently : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                                   ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-in-the-window-leniently = holdsˡᵉⁿ

  -- before the read: the lenient order banks the write's three ticks
  -- and spends them after the read; this one discards them at the match

  logged-too-early : ¬ (⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
                       ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  logged-too-early = fails

  logged-too-early-passes-leniently : ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
                                      ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  logged-too-early-passes-leniently = holdsˡᵉⁿ

  -- after the send: rejected by both, banking running forwards only

  logged-too-late : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
                      ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  logged-too-late = fails

  logged-too-late-fails-leniently : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ send ⌉ ∙ ⌈ write ⌉ ⟆
                                      ≾ˡᵉⁿ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  logged-too-late-fails-leniently = failsˡᵉⁿ

  ----------------------------------------------------------------------
  -- Time still moves freely *within* a window
  --
  -- A window is delimited by the operations the demand names, so the
  -- stretch before the first of them, and the stretch after the last,
  -- are windows too.

  -- nothing is matched before the demanded send, so the write's ticks
  -- are still available to pay for the delay in front of it

  paid-before-the-first-match : ⟅ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                                ≾ ⟅ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  paid-before-the-first-match = holds

  -- and nothing is matched after the demanded read, so a trailing
  -- demand for time is paid for by whatever the run does next

  paid-after-the-last-match : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ⟆
                              ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ⟆
  paid-after-the-last-match = holds

  ----------------------------------------------------------------------
  -- Two windows, each of which must pay for itself
  --
  -- The demand now asks for two ticks before the read and two more
  -- between the read and the send. One write in each window discharges
  -- it; two writes up front do not, though they buy the same six ticks.

  a-write-in-each-window : ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                           ≾ ⟅ ⟨ 2 ⟩ ∙ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  a-write-in-each-window = holds

  both-writes-up-front : ¬ (⟅ ⌈ write ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
                           ≾ ⟅ ⟨ 2 ⟩ ∙ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆)
  both-writes-up-front = fails

  both-writes-up-front-pass-leniently :
    ⟅ ⌈ write ⌉ ∙ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
    ≾ˡᵉⁿ ⟅ ⟨ 2 ⟩ ∙ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  both-writes-up-front-pass-leniently = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- What does not change
  --
  -- A demand naming no operation is one long window, so the two orders
  -- agree on every claim about elapsed time as such.

  read-covers-one-tick : ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 1 ⟩ ⟆
  read-covers-one-tick = holds

  read-covers-no-two : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 2 ⟩ ⟆)
  read-covers-no-two = fails

  uplink-covers-nine-ticks : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 9 ⟩ ⟆
  uplink-covers-nine-ticks = holds

  uplink-covers-no-ten : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 10 ⟩ ⟆)
  uplink-covers-no-ten = fails

  -- and an operation is still never bought with time

  idling-is-no-read : ¬ (⟅ ⟨ 100 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  idling-is-no-read = fails

  ----------------------------------------------------------------------
  -- Alternatives are read as they are over the lenient order
  --
  -- The lift is the same construction; only the relation lifted has
  -- changed. So a demand listing alternatives is discharged by covering
  -- every one of them, and a run listing alternatives discharges a
  -- demand as soon as one of them does.

  not-both-of-those : ¬ (⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                        ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 20 ⟩ ⟆)
  not-both-of-those = fails

  either-way-of-opening-it : ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                             ≾ ⟅ ⌈ read ⌉ ∣ ⟨ 10 ⟩ ⟆
  either-way-of-opening-it = holds

  -- an alternative that logs in the window discharges the demand even
  -- when the other alternative logs too early

  one-good-run-is-enough : ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉
                           ∣ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
                           ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  one-good-run-is-enough = holds

  ----------------------------------------------------------------------
  -- The unit demands nothing, so it is the greatest grade

  everything-opens-the-unit : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆
  everything-opens-the-unit =
    holds {⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} {⟅ ⟨ 0 ⟩ ⟆}

------------------------------------------------------------------------
-- A cap on what may have happened
--
-- `SubtraceTimed.LowerLift.RightSided`, the same comparison with the
-- sets in the order they are written. The grade lists alternative
-- permissions, and a run stays within it by doing at most what one of
-- them allows -- with the same window discipline, now read as a bound
-- on when the run may take its time.

module RightSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.RightSided
    Op _≟ₒ_ cost using (lower-lift-right-sided; _≾_; _≾?_) public

  open import Syntax.Grades.Example.Traces.Subtrace.LowerLift.RightSided
    Op _≟ₒ_ cost using () renaming (_≾_ to _≾ˡᵉⁿ_; _≾?_ to _≾ˡᵉⁿ?_)

  order : Grade._≾_ lower-lift-right-sided ≡ _≾_
  order = refl

  holds : {P Q : NeTraces} {p : True (P ≾? Q)} → P ≾ Q
  holds {p = p} = toWitness p

  fails : {P Q : NeTraces} {p : False (P ≾? Q)} → ¬ (P ≾ Q)
  fails {p = p} = toWitnessFalse p

  holdsˡᵉⁿ : {P Q : NeTraces} {p : True (P ≾ˡᵉⁿ? Q)} → P ≾ˡᵉⁿ Q
  holdsˡᵉⁿ {p = p} = toWitness p

  ----------------------------------------------------------------------
  -- A weaker cap permits more

  a-read-is-within-the-uplink : ⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  a-read-is-within-the-uplink = holds

  the-uplink-exceeds-a-read : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆ ≾ ⟅ ⌈ read ⌉ ⟆)
  the-uplink-exceeds-a-read = fails

  ----------------------------------------------------------------------
  -- The separation, read as a cap
  --
  -- A cap that logs between the read and the send permits the uplink
  -- schedule; one that logs before the read does not, although
  -- leniently it would.

  the-window-permits-it : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                          ≾ ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
  the-window-permits-it = holds

  logging-early-does-not : ¬ (⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                             ≾ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  logging-early-does-not = fails

  logging-early-does-leniently : ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                                 ≾ˡᵉⁿ ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆
  logging-early-does-leniently = holdsˡᵉⁿ

  ----------------------------------------------------------------------
  -- The unit permits only the instantaneous run, so it is the least
  -- grade -- which is what makes the zero-product property say
  -- something in this row

  nothing-fits-in-the-unit : ¬ (⟅ ⌈ read ⌉ ⟆ ≾ ⟅ ⟨ 0 ⟩ ⟆)
  nothing-fits-in-the-unit = fails

  the-unit-fits-anywhere : ⟅ ⟨ 0 ⟩ ⟆ ≾ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
  the-unit-fits-anywhere = holds

------------------------------------------------------------------------
-- Both at once
--
-- `SubtraceTimed.LowerLift.TwoSided`: a floor and a cap, compared in
-- opposite argument orders, with the window discipline on each
-- endpoint.

module TwoSided where

  open import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.TwoSided
    Op _≟ₒ_ cost using (TraceInterval; [_,_,_]; lo; hi; lower-lift-two-sided;
                        _≾ᵗⁱ_; _≾ᵗⁱ?_; _·ᵗⁱ_; uᵗⁱ) public

  open import Syntax.Grades.Traces.Sets Op using (traces)

  order : Grade._≾_ lower-lift-two-sided ≡ _≾ᵗⁱ_
  order = refl

  holds : (i j : TraceInterval) {p : True (i ≾ᵗⁱ? j)} → i ≾ᵗⁱ j
  holds i j {p} = toWitness p

  fails : (i j : TraceInterval) {p : False (i ≾ᵗⁱ? j)} → ¬ (i ≾ᵗⁱ j)
  fails i j {p} = toWitnessFalse p

  -- exactly one run, required and permitted

  exactly : Trace → TraceInterval
  exactly t = [ ⟅ t ⟆ , ⟅ t ⟆ , ≼ˢ-refl {traces ⟅ t ⟆} ]

  -- at least a read, at most the uplink schedule

  sensed : TraceInterval
  sensed =
    [ ⟅ ⌈ read ⌉ ⟆ , ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ⟆ ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆} tt
    ]

  ----------------------------------------------------------------------
  -- Widening at both ends weakens the grade

  exactly-a-read-sits-inside : exactly ⌈ read ⌉ ≾ᵗⁱ sensed
  exactly-a-read-sits-inside = holds (exactly ⌈ read ⌉) sensed

  -- but the uplink is not below the read-only interval: it exceeds
  -- that interval's cap

  the-uplink-does-not : ¬ (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                            ≾ᵗⁱ exactly ⌈ read ⌉)
  the-uplink-does-not =
    fails (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) (exactly ⌈ read ⌉)

  ----------------------------------------------------------------------
  -- The separation on the cap endpoint
  --
  -- Raising the cap from the uplink schedule to a run that logs between
  -- the read and the send weakens the grade; raising it to one that
  -- logs before the read does not, the two orders parting company on
  -- exactly that pair.

  logged-in-the-window : TraceInterval
  logged-in-the-window =
    [ ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
    , ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆
    , toWitness {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                    ≼ˢ? traces ⟅ ⌈ read ⌉ ∙ ⌈ write ⌉ ∙ ⌈ send ⌉ ⟆} tt
    ]

  raised-into-the-window : exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)
                           ≾ᵗⁱ logged-in-the-window
  raised-into-the-window =
    holds (exactly (⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉)) logged-in-the-window

  -- the same interval with the write moved before the read is not even
  -- an interval for this order: its floor does not sit inside its cap,
  -- so the consistency field cannot be filled -- which is the two-sided
  -- reading of `LeftSided.logged-too-early`

  ¬logged-too-early : ¬ (traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                         ≼ˢ traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆)
  ¬logged-too-early =
    toWitnessFalse {a? = traces ⟅ ⌈ read ⌉ ∙ ⟨ 2 ⟩ ∙ ⌈ send ⌉ ⟆
                       ≼ˢ? traces ⟅ ⌈ write ⌉ ∙ ⌈ read ⌉ ∙ ⌈ send ⌉ ⟆} tt

  ----------------------------------------------------------------------
  -- The unit is the interval that requires and permits nothing

  the-unit : uᵗⁱ ≡ [ ⟅ ⟨ 0 ⟩ ⟆ , ⟅ ⟨ 0 ⟩ ⟆ , ≼ˢ-refl {traces ⟅ ⟨ 0 ⟩ ⟆} ]
  the-unit = refl

  nothing-but-the-unit-is-below-it : ¬ (exactly ⌈ read ⌉ ≾ᵗⁱ uᵗⁱ)
  nothing-but-the-unit-is-below-it = fails (exactly ⌈ read ⌉) uᵗⁱ
