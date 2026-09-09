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
-- Each trace grade has a frame of either kind, and reading the two     --
-- against each other is how the tick worlds' blindness shows: they see --
-- a grade only through durations, so distinctions the histories keep   --
-- collapse. The frames that went with the earlier grid are parked      --
-- under `backup/` and imported from nowhere.                           --
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

-- advance no further than one of the bounds a trace grade lists: the
-- right-sided interval frame, with the bound read off a trace

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.RightSided

-- advance at least as far as one of the guarantees a trace grade lists:
-- the mirror image, with the bound read off a trace

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.LeftSided

-- both at once, the two witnesses independent

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Timed.TwoSided

-- the same three at the subset order. The quantifier over the listed
-- runs follows the direction of inclusion the grade weakens along, so
-- the cap's frame is existential and the floor's universal -- the
-- floor's condition being asked of every demanded run, which is what
-- makes a tick world read it as "at least as long as the slowest"

import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.RightSided
import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.LeftSided
import DenotationalSemantics.Model.Example.World.Ticks.Traces.Subsets.TwoSided

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

-- the same three at the subset order, where accessibility is membership
-- outright, there being no comparison between the continuation and a
-- listed run to make. The floor's frame is the informative one: it asks
-- every demanded run to *be* the continuation, so a non-singleton grade
-- reaches no world at all -- one history is one run, and cannot be two.
-- The tick frame cannot see that, several demanded runs collapsing
-- there into their slowest

import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.RightSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.LeftSided
import DenotationalSemantics.Model.Example.World.TraceHistory.Traces.Subsets.TwoSided
