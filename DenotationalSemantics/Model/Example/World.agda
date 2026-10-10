------------------------------------------------------------------------
-- Concrete Kripke frames of worlds.                                  --
--                                                                    --
-- A `World` (see `DenotationalSemantics.Model.World`) is a set of    --
-- worlds with a resource-graded accessibility relation `_⊑[ ρ ]_`    --
-- that is reflexive at the unit grade, transitive with the grades    --
-- multiplying, covariant in the grade, and proof-irrelevant. The     --
-- frames below differ in what a world records.                       --
--                                                                    --
-- The frames form four families:                                     --
--                                                                    --
--   * `Ticks.*`: a world is a time point, in `ℕ` or, for dense time, --
--     in `ℚ≥0`, recording the elapsed time. Accessibility bounds how --
--     far ahead the grade moves: an exact tick for a grade that      --
--     fixes a duration, a window for one that bounds it.             --
--                                                                    --
--   * `Tallies.*`: a world is a tally of how often each counter has  --
--     been drawn on, a time point per counter.                       --
--                                                                    --
--   * `Labels.*`: a world is the security label reached so far,      --
--     rising as the grade allows.                                    --
--                                                                    --
--   * `TraceHistory.*`: a world is a timed trace, the history        --
--     observed so far, recording the operations as well as their     --
--     duration. Accessibility appends a continuation that the grade  --
--     admits, so these frames distinguish the operations a grade     --
--     prescribes, which the tick frames do not.                      --
--                                                                    --
-- The tick, tally and label frames are instances of one construction --
-- (`DenotationalSemantics.Model.World.Action`): the grade acting by  --
-- multiplication on the points it measures, `w ⊑[ ρ ] w'` iff        --
-- `w' ≾ w · ρ`. Its restriction `forward` adds `w ≤ w'`, and every   --
-- frame bounded only from above (the right-sided ticks, the at-most  --
-- tallies, the labels) uses it. No frame reaches the past: a lower   --
-- bound keeps the other frames forward, and an adjoined greatest     --
-- grade reaches exactly the worlds ahead. `Product.*` pairs frames   --
-- componentwise (`DenotationalSemantics.Model.World.Product`).       --
--                                                                    --
-- The timed and finite-subset trace grades have a frame of either    --
-- kind; the tick frames see a grade only through durations, and      --
-- identify distinctions that the history frames keep.                --
--                                                                    --
-- The module is an index: the trace-based frames are parameterised   --
-- by the alphabet `Op`, and are listed rather than re-exported.      --
------------------------------------------------------------------------

module DenotationalSemantics.Model.Example.World where

------------------------------------------------------------------------
-- Time-ticks frames: worlds are time points
--
-- `w ⊑ᵗ[ ρ ] w'` locates `w'` ahead of `w` by as much time as `ρ`
-- allows. A tick world records no operations, so a grade that
-- prescribes them is read only through their durations.

-- reach every world at least `n` ticks ahead

import DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSided

-- reach the worlds ahead by at most `n` ticks, never behind: the mirror
-- image

import DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided

-- reach the worlds inside the window `[ min , max ]` ticks ahead, with
-- an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.Ticks.Time.TwoSidedWithInfinity

-- the same two with a formal greatest grade adjoined, which reaches
-- every world ahead: the greatest forward relation, containing every
-- other, as covariance requires, and closed under composition, the
-- adjoined point being absorbing

import DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSidedWithTop
import DenotationalSemantics.Model.Example.World.Ticks.Time.TwoSidedWithInfinityAndTop

-- advance no further than one of the bounds a trace grade lists: the
-- right-sided interval frame, with the bound read off a trace

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.RightSided

-- advance at least as far as one of the guarantees a trace grade lists:
-- the mirror image, with the bound read off a trace

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.LeftSided

-- both at once, the two witnesses independent

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.TwoSided

-- the cap at the subset order. The quantifier over the listed runs is
-- existential, following the direction in which the grade weakens:
-- moving forward takes no longer than one of the listed runs

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided

------------------------------------------------------------------------
-- Trace-history frames: worlds are timed traces
--
-- `w ⊑ʰ[ ρ ] w'` asks for a continuation `cont` with `w ∙ cont ≡ w'`
-- that the grade `ρ` admits. The relation is a Σ-type and is covariant
-- in the grade up to equality.

-- append a continuation whose duration falls in `[ min , max ]`, with
-- an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinity

-- the same with a formal greatest grade adjoined, which reaches every
-- history extending the current one: the greatest forward relation

import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinityAndTop

-- append a continuation that stays within one of the bounds a trace
-- grade lists: accessibility is "the continuation is a run the grade
-- admits"

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.RightSided

-- append a continuation that covers one of the guarantees a trace grade
-- lists: the comparison runs the other way round

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.LeftSided

-- append one continuation answering to both endpoints at once, which a
-- history frame expresses and a tick frame does not

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.TwoSided

-- the cap at the subset order, where accessibility is membership, with
-- no comparison between the continuation and a listed run. The frame is
-- as fine as the grade, distinguishing runs that the tick frame
-- identifies by their durations

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.RightSided

------------------------------------------------------------------------
-- Dense time-ticks frames: worlds are points of `ℚ≥0`
--
-- The discrete tick frames' relations over dense time, each the action
-- frame of its grade at the points.

-- reach every world at least `q` ahead

import DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.LeftSided

-- reach the worlds ahead by at most `a`, never behind

import DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.RightSided

-- reach the worlds inside the window `[ p , a ]` ahead

import DenotationalSemantics.Model.Example.World.Ticks.Time.Dense.TwoSided

------------------------------------------------------------------------
-- Tally frames: worlds are per-counter tallies
--
-- `ws ⊑[ ks ] ws'` holds on each counter separately: the power of a
-- tick frame, one time point per counter.

-- the power of a frame, for the power of a grade

import DenotationalSemantics.Model.Example.World.Tallies.Counts.Power

-- a quota: each tally rises by at most its bound

import DenotationalSemantics.Model.Example.World.Tallies.Counts.AtMost

-- a guarantee: each tally rises by at least its bound

import DenotationalSemantics.Model.Example.World.Tallies.Counts.AtLeast

------------------------------------------------------------------------
-- Label frames: worlds are security labels
--
-- `w ⊑ˡ[ ℓ ] w'` iff `w ⊑ w' ⊑ w ∨ ℓ`: the label floats up, by at most
-- `ℓ`; at `Low < High` and at taint sets

import DenotationalSemantics.Model.Example.World.Labels.SecurityLevel

------------------------------------------------------------------------
-- Product frames: worlds are pairs
--
-- one frame per component, accessibility componentwise

-- time points and labels: an embargo with a taint check

import DenotationalSemantics.Model.Example.World.Product.LeftSidedTimeLevel

-- time points and labels: an expiring, untainted capability

import DenotationalSemantics.Model.Example.World.Product.RightSidedTimeLevel

-- time points and energy spent, the energy frame being the time frame
-- along the identity, which ignores `of-dur`

import DenotationalSemantics.Model.Example.World.Product.RightSidedTimeEnergy

------------------------------------------------------------------------
-- Trace-history frames over regular sets of runs

-- append a continuation whose encoding the language contains:
-- membership outright, as for the finite subsets

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Regular.RightSided
