------------------------------------------------------------------------
-- Concrete Kripke frames of worlds.                                  --
--                                                                    --
-- A `World` (see                                                     --
-- `MonomorphicCalculus.DenotationalSemantics.Model.World`) is a set  --
-- of worlds with a resource-graded accessibility relation `_⊑[ ρ ]_` --
-- that is reflexive at the unit grade, transitive with the grades    --
-- multiplying, covariant in the grade, and proof-irrelevant. The     --
-- frames below differ in what a world records.                       --
--                                                                    --
-- The frames form four families:                                     --
--                                                                    --
--   * `Ticks.*`: a world is a time point, in `ℕ` or, for rational    --
--     time, in `ℚ≥0`, recording the elapsed time. Accessibility      --
--     bounds how far ahead the grade moves: an exact tick for a      --
--     grade that fixes a duration, a window for one that bounds it.  --
--                                                                    --
--   * `Tallies.*`: a world is a tally of how often each counter has  --
--     been drawn on, a time point per counter.                       --
--                                                                    --
--   * `Labels.*`: a world is the level of the lattice reached so     --
--     far, rising as the grade allows.                               --
--                                                                    --
--   * `TraceHistory.*`: a world is a timed trace, the history        --
--     observed so far, recording the operations as well as their     --
--     duration. Accessibility appends a continuation that the grade  --
--     admits, so these frames distinguish the operations a grade     --
--     prescribes, which the tick frames do not.                      --
--                                                                    --
-- The label frames and the tick frames of `Ticks.Time.Rational` are  --
-- built from one construction                                        --
-- (`MonomorphicCalculus.DenotationalSemantics.Model.World.Action`):  --
-- the grade acting by multiplication on the points it measures,      --
-- `w ⊑[ ρ ] w'` iff `w' ≾ w · ρ`. Its restriction                    --
-- `forward` adds `w ≤ w'`, and every frame bounded only from above   --
-- (the upper-bound ticks, the at-most tallies, the labels) uses it.  --
-- No frame reaches the past: a lower bound keeps the other frames    --
-- forward, and an adjoined greatest grade reaches exactly the worlds --
-- ahead. `Product.*` pairs frames componentwise                      --
-- (`MonomorphicCalculus.DenotationalSemantics.Model.World.Product`). --
--                                                                    --
-- The timed regex grades share one history frame                     --
-- (`MonomorphicCalculus.DenotationalSemantics.Model.World.History`): --
-- a continuation is read in the grade, operations by their grades    --
-- and delays by `ι`, and is admitted when its reading is below the   --
-- grade.                                                             --
--                                                                    --
-- The trace grades with banked delays and the finite run sets have a --
-- frame of either kind; the tick frames see a grade only through     --
-- durations, and identify distinctions that the history frames keep. --
--                                                                    --
-- The module is an index: the trace-based frames are parameterised   --
-- by the alphabet `Op`, and are listed rather than re-exported.      --
------------------------------------------------------------------------

module MonomorphicCalculus.DenotationalSemantics.Model.Example.World where

------------------------------------------------------------------------
-- Time-ticks frames: worlds are time points
--
-- `w ⊑ᵗ[ ρ ] w'` locates `w'` ahead of `w` by as much time as `ρ`
-- allows. A tick world records no operations, so a grade that
-- prescribes them is read only through their durations.

-- reach every world at least `n` ticks ahead

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.LowerBound

-- reach the worlds ahead by at most `n` ticks, never behind: the mirror
-- image

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.UpperBound

-- reach the worlds inside the window `[ min , max ]` ticks ahead, with
-- an infinite `max` imposing no upper bound

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Interval

-- the same two with a formal greatest grade adjoined, which reaches
-- every world ahead: the greatest forward relation, containing every
-- other, as covariance requires, and closed under composition, the
-- adjoined point being absorbing

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.LowerBoundWithTop
import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.IntervalWithTop

-- advance no further than one of the bounds a trace grade lists: the
-- upper bound frame, with the bound read off a trace; these
-- three are over any time domain, worlds being its time points

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.Banked.UpperBound

-- advance at least as far as one of the guarantees a trace grade lists:
-- the mirror image, with the bound read off a trace

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.Banked.LowerBound

-- both at once, the two witnesses independent

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.Banked.Interval

-- the finite run set cap. The quantifier over the listed runs is
-- existential, following the direction in which the grade weakens:
-- moving forward takes no longer than one of the listed runs

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Traces.FiniteRunSets.UpperBound

------------------------------------------------------------------------
-- Trace-history frames: worlds are timed traces
--
-- `w ⊑ʰ[ ρ ] w'` asks for a continuation `cont` with `w ∙ cont ≡ w'`
-- that the grade `ρ` admits. The relation is a Σ-type and is covariant
-- in the grade up to equality.

-- append a continuation whose duration falls in `[ min , max ]`, with
-- an infinite `max` imposing no upper bound

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Time.Interval

-- the same with a formal greatest grade adjoined, which reaches every
-- history extending the current one: the greatest forward relation

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Time.IntervalWithTop

-- append a continuation that stays within one of the bounds a trace
-- grade lists: accessibility is "the continuation is a run the grade
-- admits"

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Banked.UpperBound

-- append a continuation that covers one of the guarantees a trace grade
-- lists: the comparison runs the other way round

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Banked.LowerBound

-- append one continuation answering to both endpoints at once, which a
-- history frame expresses and a tick frame does not

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Banked.Interval

-- the finite run set cap, where accessibility is membership, with no
-- comparison between the continuation and a listed run. The frame is
-- as fine as the grade, distinguishing runs that the tick frame
-- identifies by their durations

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.FiniteRunSets.UpperBound

------------------------------------------------------------------------
-- Rational time-ticks frames: worlds are points of `ℚ≥0`
--
-- The discrete tick frames' relations over rational time, each the
-- action frame of its grade at the points.

-- reach every world at least `q` ahead

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Rational.LowerBound

-- reach the worlds ahead by at most `a`, never behind

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Rational.UpperBound

-- reach the worlds ahead by a duration the interval admits, its ends
-- open or closed

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Ticks.Time.Rational.Interval

------------------------------------------------------------------------
-- Tally frames: worlds are per-counter tallies
--
-- `ws ⊑[ ks ] ws'` holds on each counter separately: the power of a
-- tick frame, one time point per counter.

-- the power of a frame, for the power of a grade

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.Power

-- at-most counts: each tally rises by at most its bound

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.AtMost

-- at-least counts: each tally rises by at least its bound

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Tallies.Counts.AtLeast

------------------------------------------------------------------------
-- Label frames: worlds are levels of a lattice
--
-- `w ⊑ˡ[ ℓ ] w'` iff `w ⊑ w' ⊑ w ∨ ℓ`: the label floats up, by at most
-- `ℓ`; at `Low < High` and at taint sets

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Labels.Lattice

------------------------------------------------------------------------
-- Product frames: worlds are pairs
--
-- one frame per component, accessibility componentwise

-- time points and labels: an embargo with a taint check

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Product.TimeLowerBoundLattice

-- time points and labels: an expiring, untainted capability

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Product.TimeUpperBoundLattice

-- time points and energy spent, the energy frame being the time frame
-- along the identity, which ignores `ι`

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.Product.TimeUpperBoundEnergy

------------------------------------------------------------------------
-- Trace-history frames over regular trace languages

-- append a continuation whose encoding the language contains:
-- membership outright, as for the finite run sets

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Regular.UpperBound

------------------------------------------------------------------------
-- Trace-history frames for the timed regex grades
--
-- `w ⊑ʰ[ ρ ] w'` asks for a continuation `s` with `w ∙ s ≡ w'` whose
-- reading in the grade is below `ρ`; at an interval one continuation
-- answers to both endpoints.

-- the timed regex grades in whole steps; every operation admits a whole
-- number of steps

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Nat.UpperBound
import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Nat.LowerBound
import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Nat.Interval

-- the finite timed regex grades; accessibility is shown to be the
-- reading the order gives: every exact word of the continuation's run
-- fits a word of the grade

import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Finite.UpperBound
import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Finite.LowerBound
import MonomorphicCalculus.DenotationalSemantics.Model.Example.World.TraceHistory.Traces.TimedRegex.Finite.Interval
