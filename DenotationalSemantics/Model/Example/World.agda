------------------------------------------------------------------------
-- Concrete Kripke frames of worlds.                                   --
--                                                                     --
-- A `World` (see `DenotationalSemantics.Model.World`) is a bare set of --
-- worlds together with a resource-graded accessibility `_⊑[ ρ ]_`      --
-- that is reflexive at the unit grade, transitive with the grades      --
-- multiplying, covariant in the grade, and proof-irrelevant. Building  --
-- one for a given grade is exactly the question of what a world has to --
-- remember for the grade to say something about moving between worlds. --
--                                                                     --
-- The frames come in four families, one per answer:                   --
--                                                                     --
--   * `Ticks.*` -- a world is a time point, in `ℕ` or, for dense time, --
--     in `ℚ≥0`. It remembers only how much time has elapsed, so        --
--     accessibility says how far ahead the grade may move: an exact    --
--     tick for a grade that fixes a duration, a window for one that    --
--     only bounds it.                                                  --
--                                                                     --
--   * `Tallies.*` -- a world is a tally, how often each counter has    --
--     been drawn on: a time point per counter.                         --
--                                                                     --
--   * `Labels.*` -- a world is the security label reached so far,      --
--     floating upward as the grade allows.                             --
--                                                                     --
--   * `TraceHistory.*` -- a world is a timed trace, the history        --
--     observed so far. It remembers *what happened*, not just how      --
--     long it took, so accessibility appends a continuation the grade  --
--     admits. These frames see the operations a grade prescribes,      --
--     which the tick frames cannot.                                    --
--                                                                     --
-- The tick, tally and label frames rest on one construction           --
-- (`DenotationalSemantics.Model.World.Action`): the grade acting by    --
-- multiplication on the points it measures, `w ⊑[ ρ ] w'` iff          --
-- `w' ≾ w · ρ`. Its `forward` restriction adds `w ≤ w'`, and every    --
-- frame bounded only from above -- the right-sided ticks, the at-most  --
-- tallies, the labels -- uses it. No frame reaches the past: a lower   --
-- bound keeps the others forward, and an adjoined greatest grade       --
-- reaches exactly the worlds ahead.                                    --
-- `Product.*` pairs frames componentwise                               --
-- (`DenotationalSemantics.Model.World.Product`).                       --
--                                                                     --
-- The timed and finite-subset trace grades have a frame of either      --
-- kind, and reading the two against each other is how the tick worlds' --
-- blindness shows: they see a grade only through durations, so         --
-- distinctions the histories keep collapse. Frames for the             --
-- sub-trace-order grid are parked under `backup/` and imported from    --
-- nowhere.                                                             --
--                                                                     --
-- This module is only an index -- the trace-based frames are           --
-- parameterised by the alphabet `Op`, so it lists the pieces rather    --
-- than re-exporting them.                                              --
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
-- other as covariance asks, and composition survives because the
-- adjoined point absorbs

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

-- the cap at the subset order. The quantifier over the listed runs
-- follows the direction of inclusion the grade weakens along, so this
-- frame is existential: moving forward may take no longer than one of
-- the listed runs

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided

------------------------------------------------------------------------
-- Trace-history frames: worlds are timed traces
--
-- `w ⊑ʰ[ ρ ] w'` asks for a continuation `cont` with `w ∙ cont ≡ w'`
-- that the grade `ρ` admits. Being Σ-shaped, the relation is covariant
-- in the grade on the nose.

-- append a continuation whose duration falls in `[ min , max ]`, with
-- an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinity

-- the same with a formal greatest grade adjoined, which reaches every
-- history extending the current one: the greatest forward relation

import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinityAndTop

-- append a continuation that stays within one of the bounds a trace
-- grade lists -- accessibility is then just "the continuation is a run
-- the grade admits"

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.RightSided

-- append a continuation that covers one of the guarantees a trace grade
-- lists: the comparison runs the other way round

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.LeftSided

-- append one continuation answering to both endpoints at once, which is
-- what a history frame can say and a tick frame cannot

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Timed.TwoSided

-- the cap at the subset order, where accessibility is membership
-- outright, there being no comparison between the continuation and a
-- listed run to make. The frame is then as fine-grained as the grade
-- is, distinguishing runs the tick frame collapses into their durations

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
-- along the identity, which ignores `of-nat`

import DenotationalSemantics.Model.Example.World.Product.RightSidedTimeEnergy

------------------------------------------------------------------------
-- Trace-history frames over regular sets of runs

-- append a continuation whose encoding the language contains:
-- membership outright, as for the finite subsets

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Regular.RightSided
