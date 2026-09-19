------------------------------------------------------------------------
-- Typed example computations, one grade at a time.                    --
--                                                                     --
-- The rest of this subtree exhibits orderings between grades; this    --
-- one puts the grades to work. It fixes a language over the sensor    --
-- node's alphabet and writes example computations in it, each typed   --
-- against a value type and an effect grade, so that what a grade      --
-- permits is settled by whether a program typechecks.                 --
--                                                                     --
-- Every instance uses an identity grade system -- effect and resource --
-- grades are the same monoid and `∣_∣ᵉ` is the identity -- so `mapᵉ`  --
-- disappears: the lock a computation puts on the context is its own   --
-- effect grade, and `unbox`'s premise compares what a computation did --
-- with the grade on the box. The instances differ only in that        --
-- monoid.                                                             --
--                                                                     --
-- Comments inside the programs say what each former appends to the    --
-- context its subcomputation is typed in: `⟨ ρ ⟩` a lock, `∷ A` a     --
-- binding. Reading them off downwards gives the context at any point, --
-- and the locks between a box's binding and its `unbox` are the       --
-- elapsed grade the premise weighs against the box's own.             --
--                                                                     --
-- Each instance writes its programs out in full, at its own grades,   --
-- with every side condition discharged where the rule imposes it, by  --
-- running the grade's own decision procedure. A program the grade     --
-- refuses is not written; in its place stands a refutation of the     --
-- bound it would have needed. `Typing/Core.agda` holds what the       --
-- programs are written *with*: the language, the three ways of        --
-- meeting `var`'s bound, and the operation clauses handed to          --
-- `handle`.                                                           --
--                                                                     --
-- Two rules put the unit on opposite sides of the order, and each     --
-- instance settles both as a proof or a refutation: whether a         --
-- non-eternal variable goes stale, which is `var`'s bound `ρ ≾ᵣ uᵣ`,  --
-- and whether a handler clause may drop its continuation.             --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Typing where

-- The language the examples are written in -- base types, operation
-- signature, and the programs themselves, parameterised by the grade
-- and by what it gives each operation.

import Syntax.Grades.Example.Worked.Typing.Core

------------------------------------------------------------------------
-- Grades that measure time

-- "at least `n` time steps": a box is a resource that becomes
-- available, and nothing goes stale

import Syntax.Grades.Example.Worked.Typing.Time.LeftSided

-- "at most `n` time steps": a box is a lease that expires, and a
-- reading goes stale as soon as anything happens

import Syntax.Grades.Example.Worked.Typing.Time.RightSided

-- both bounds at once: a box has a window, and a claim can be made too
-- early or too late

import Syntax.Grades.Example.Worked.Typing.Time.TwoSided

------------------------------------------------------------------------
-- Grades that record which runs there were
--
-- The same programs against grades that see which operations ran and
-- where, at the three orders of each family.

-- sets of traces at the coverage order: a box asks for work to have
-- been done, and time cannot stand in for it

import Syntax.Grades.Example.Worked.Typing.Traces.Timed.LeftSided

-- at the allowance order: a box permits particular runs, so a claim can
-- be refused over which operations were performed and where

import Syntax.Grades.Example.Worked.Typing.Traces.Timed.RightSided

-- at both: a box asks for work and caps what may have happened since

import Syntax.Grades.Example.Worked.Typing.Traces.Timed.TwoSided

-- the subset order as a floor: a box names the run that must have
-- happened, and `if` loses its branches

import Syntax.Grades.Example.Worked.Typing.Traces.Subsets.LeftSided

-- the same floor at a signature that grades one operation by several
-- runs, which is where a conjunctive floor's non-singleton grades come
-- from: a transmitter that may retry

import Syntax.Grades.Example.Worked.Typing.Traces.Subsets.LeftSided.Retrying

-- as a cap: a box names the runs it covers outright, nothing paying for
-- anything else

import Syntax.Grades.Example.Worked.Typing.Traces.Subsets.RightSided

-- and as both, the Egli-Milner reading, which against this calculus
-- behaves as the floor alone

import Syntax.Grades.Example.Worked.Typing.Traces.Subsets.TwoSided
