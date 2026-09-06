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

import DenotationalSemantics.Model.Example.World.Ticks.Time.LeftSided

-- reach the worlds at most `n` ticks ahead: the mirror image

import DenotationalSemantics.Model.Example.World.Ticks.Time.RightSided

-- reach the worlds inside the window `[ min , max ]` ticks ahead

import DenotationalSemantics.Model.Example.World.Ticks.Time.TwoSided

-- the same, with an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.Ticks.Time.TwoSidedWithInfinity

-- reach the worlds an *exact* trace duration ahead: the grade's traces
-- are compared by inclusion, so each names one admissible duration

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Inclusion.RightSided

-- reach *at least* a trace duration ahead: the sub-trace order reads a
-- grade as a floor, so the reach has the left-sided interval's shape

import DenotationalSemantics.Model.Example.World.Ticks.Traces.LowerLift.LeftSided

-- advance at most a cap-trace's duration ahead: the right-sided
-- interval frame, with the bound read off a trace of the grade

import DenotationalSemantics.Model.Example.World.Ticks.Traces.LowerLift.RightSided

-- reach into the window between a floor-trace's and a cap-trace's
-- duration: the two-sided interval frame, with both endpoints read off
-- traces

import DenotationalSemantics.Model.Example.World.Ticks.Traces.LowerLift.TwoSided

-- the Smyth-lift floor: a continuation covering *some* listed demand,
-- which is the reading that order -- and not the lower lift's -- is
-- covariant for

import DenotationalSemantics.Model.Example.World.Ticks.Traces.UpperLift.LeftSided

------------------------------------------------------------------------
-- Trace-history frames: worlds are timed traces
--
-- `w ⊑ʰ[ ρ ] w'` asks for a continuation `cont` with `w ∙ cont ≡ w'`
-- that the grade `ρ` admits. Being Σ-shaped, the relation is covariant
-- in the grade on the nose.

-- append a continuation whose duration falls in `[ min , max ]`

import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSided

-- the same, with an infinite `max` imposing no upper bound

import DenotationalSemantics.Model.Example.World.TraceHistory.Time.TwoSidedWithInfinity

-- append a continuation that is a member of the grade

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Inclusion.RightSided

-- the exact floor and the exact pair: universal where the cap is
-- existential, since the floor's order runs over the other set

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Inclusion.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Inclusion.TwoSided

-- append a continuation that has some member of the grade inside it

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.LeftSided

-- the convex order reaches the same worlds: only its Smyth half is read
-- by the frame, the Hoare half constraining which coercions exist

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Convex.LeftSided

-- a stricter reading of the convex grade, asking the continuation to
-- cover *some* demand and to take at least *every* demand's time

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Convex.LeftSidedMayMust

-- append a continuation that stays within some member of the cap

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.RightSided

-- append a continuation bounded on both sides: it covers a member of
-- the floor and stays within a member of the cap

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.LowerLift.TwoSided

-- the Smyth-lift floor and cap: the quantifier swaps sides with the
-- order's, so the floor is existential here and the cap universal --
-- the exact mirror of the lower-lift pair above

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.UpperLift.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.UpperLift.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.UpperLift.TwoSided

-- the convex cap, reading the Hoare conjunct of its order

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Convex.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Convex.TwoSided
