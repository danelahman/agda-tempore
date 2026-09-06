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
-- The frames over a lifted trace order are built once, in              --
-- `Traces.Lifted.*`, and instantiated at each of the two sub-trace     --
-- orders -- `Traces.Subtrace.*` and `Traces.SubtraceTimed.*` -- just   --
-- as the grades themselves are. Nothing in those constructions reads   --
-- the order beyond its `TraceOrder` interface and, for the tick        --
-- frames, monotonicity of the duration, so the time-strict grades      --
-- carry exactly the frames the lenient ones do.                        --
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

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subtrace.LowerLift.LeftSided

-- advance at most a cap-trace's duration ahead: the right-sided
-- interval frame, with the bound read off a trace of the grade

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subtrace.LowerLift.RightSided

-- reach into the window between a floor-trace's and a cap-trace's
-- duration: the two-sided interval frame, with both endpoints read off
-- traces

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subtrace.LowerLift.TwoSided

-- the Smyth-lift floor: a continuation covering *some* listed demand,
-- which is the reading that order -- and not the lower lift's -- is
-- covariant for

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subtrace.UpperLift.LeftSided

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

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.LowerLift.LeftSided

-- the convex order reaches the same worlds: only its Smyth half is read
-- by the frame, the Hoare half constraining which coercions exist

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.Convex.LeftSided

-- a stricter reading of the convex grade, asking the continuation to
-- cover *some* demand and to take at least *every* demand's time

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.Convex.LeftSidedMayMust

-- append a continuation that stays within some member of the cap

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.LowerLift.RightSided

-- append a continuation bounded on both sides: it covers a member of
-- the floor and stays within a member of the cap

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.LowerLift.TwoSided

-- the Smyth-lift floor and cap: the quantifier swaps sides with the
-- order's, so the floor is existential here and the cap universal --
-- the exact mirror of the lower-lift pair above

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.UpperLift.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.UpperLift.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.UpperLift.TwoSided

-- the convex cap, reading the Hoare conjunct of its order

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.Convex.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subtrace.Convex.TwoSided

------------------------------------------------------------------------
-- The same frames over the time-strict sub-trace order
--
-- Each is `Traces.Lifted.*` at `SubtraceTimed`'s `_≼ᵗ_` instead of
-- `Subtrace`'s `_≼_`. The frame conditions are the same conditions --
-- reflexivity at the unit, transitivity multiplying the grades,
-- covariance, irrelevance -- and they hold for the same reasons, so
-- restricting when a run may spend its time costs no frame.

-- time-ticks frames

import DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.LowerLift.LeftSided
import DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.LowerLift.RightSided
import DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.LowerLift.TwoSided
import DenotationalSemantics.Model.Example.World.Ticks.Traces.SubtraceTimed.UpperLift.LeftSided

-- trace-history frames

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.LowerLift.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.LowerLift.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.LowerLift.TwoSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.UpperLift.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.UpperLift.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.UpperLift.TwoSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Convex.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Convex.LeftSidedMayMust
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Convex.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.SubtraceTimed.Convex.TwoSided
