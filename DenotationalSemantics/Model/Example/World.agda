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
-- The frames come in two families, one per answer:                     --
--                                                                     --
--   * `Ticks.*` -- a world is a time point `ℕ`. It remembers only how  --
--     much time has elapsed, so accessibility says how far ahead the   --
--     grade may move: an exact tick for a grade that fixes a duration, --
--     a window for one that only bounds it.                            --
--                                                                     --
--   * `TraceHistory.*` -- a world is a timed trace, the history        --
--     observed so far. It remembers *what happened*, not just how      --
--     long it took, so accessibility appends a continuation the grade  --
--     admits. These frames see the operations a grade prescribes,      --
--     which the tick frames cannot.                                    --
--                                                                     --
-- Both families are indexed by the grade they are a frame for, so the  --
-- two lists below run in parallel: the same grade appears once in      --
-- each, once read as elapsed time and once as observed history.        --
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

import DenotationalSemantics.Model.Example.World.Ticks.LeftSidedIntervals

-- reach the worlds inside the window `[ min , max ]` ticks ahead

import DenotationalSemantics.Model.Example.World.Ticks.TwoSidedIntervals

-- the same, with an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.Ticks.TwoSidedIntervalsWithInfinity

-- reach the worlds an *exact* trace duration ahead: the grade's traces
-- are compared by inclusion, so each names one admissible duration

import DenotationalSemantics.Model.Example.World.Ticks.SetOfTraces

-- reach *anything up to* a trace duration ahead: the sub-trace order
-- lets a run shrink inside its schedule, so the reach is a window

import DenotationalSemantics.Model.Example.World.Ticks.SetOfTracesUpToSubtrace

------------------------------------------------------------------------
-- Trace-history frames: worlds are timed traces
--
-- `w ⊑ʰ[ ρ ] w'` asks for a continuation `cont` with `w ∙ cont ≡ w'`
-- that the grade `ρ` admits. Being Σ-shaped, the relation is covariant
-- in the grade on the nose.

-- append a continuation whose duration falls in `[ min , max ]`

import DenotationalSemantics.Model.Example.World.TraceHistory.TwoSidedIntervals

-- the same, with an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.TraceHistory.TwoSidedIntervalsWithInfinity

-- append a continuation that is a member of the grade

import DenotationalSemantics.Model.Example.World.TraceHistory.SetOfTraces

-- append a continuation that is a sub-trace of some member

import DenotationalSemantics.Model.Example.World.TraceHistory.SetOfTracesUpToSubtrace

-- the convex order reaches the same worlds: only its Hoare half is read
-- by the frame, the Smyth half constraining which coercions exist

import DenotationalSemantics.Model.Example.World.TraceHistory.SetOfTracesConvex

-- a stricter reading of the convex grade, asking the continuation to be
-- permitted by *some* schedule and within *every* schedule's budget

import DenotationalSemantics.Model.Example.World.TraceHistory.SetOfTracesConvexMayMust
