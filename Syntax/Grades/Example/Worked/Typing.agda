------------------------------------------------------------------------
-- Typed example computations, one grade at a time.                     --
--                                                                     --
-- The rest of this subtree exhibits orderings between grades. This one --
-- puts the grades to work: it fixes a language over the sensor node's  --
-- alphabet and writes example computations in it, each typed against a --
-- value type and an effect grade, so that what a grade permits is      --
-- settled by whether a program typechecks.                             --
--                                                                     --
-- Every instance uses an *identity* grade system -- effect grades and  --
-- resource grades are the same monoid, and `∣_∣ᵉ` is the identity --   --
-- so `mapᵉ` disappears and the rules read directly: the lock a         --
-- computation puts on the context is its own effect grade, and         --
-- `unbox`'s premise compares what a computation did with the grade on  --
-- the box. The instances differ only in that monoid.                   --
--                                                                     --
-- READING A PROGRAM. Comments inside the programs say what each        --
-- former appends to the context its subcomputation is typed in:        --
-- `⟨ ρ ⟩` a lock, `∷ A` a binding. `perform` and `delay` put up a lock --
-- and `perform` binds a result; `⨟` and `handle`'s `in` part put up a  --
-- lock at the grade the part before them was *typed at* and bind its   --
-- result; `box`, `unbox`, `lam` and `match` bind without locking; `if` --
-- and `coerce` do neither. Reading the comments off downwards gives    --
-- the context at any point, and the locks between a box's binding and  --
-- its `unbox` are the elapsed grade the premise weighs against the     --
-- box's own.                                                           --
--                                                                     --
-- Each instance writes its programs out in full, at its own grades,    --
-- with every side condition discharged where the rule imposes it, by   --
-- running the grade's own decision procedure. A program the grade      --
-- refuses is not written; what stands in its place is a refutation of  --
-- the bound it would have needed. `Typing/Core.agda` holds what the    --
-- programs are written *with*: the language, the three ways of meeting --
-- `var`'s bound, and the operation clauses handed to `handle`.         --
--                                                                     --
-- Two rules put the unit on opposite sides of the order, and each      --
-- instance settles them independently:                                 --
--                                                                     --
--   `var`'s bound is `ρ ≾ᵣ uᵣ` -- is what elapsed below the unit? If   --
--   not, a non-eternal variable goes stale as soon as that much has    --
--   happened, and data that is to survive has to be boxed.             --
--                                                                     --
--   a clause that drops its continuation needs `uₑ ≾ₑ op-grade op ·ₑ   --
--   ε''` -- is the unit below the clause's grade? If not, no handler   --
--   clause may discard the computation it is handling.                 --
--                                                                     --
--                       goes stale?   may discard?                     --
--   lower bounds        no            no                               --
--   upper bounds        yes           yes                              --
--   windows             yes           no                               --
--   trace guarantees    no            no                               --
--   trace allowances    yes           yes                              --
--   trace contracts     yes           no                               --
--   demanded runs       yes           no                               --
--   listed runs         yes           no                               --
--   Egli-Milner         yes           no                               --
--                                                                     --
-- Each entry is a proof or a refutation in the instance concerned.     --
--                                                                     --
-- A third rule meets `unbox` obliquely. Sequencing types its           --
-- continuation under the lock `⟨ mapᵉ ε ⟩`, `ε` being the grade its    --
-- first part is *typed at*, so a `coerce` there changes what the       --
-- continuation may claim -- and only ever for the worse, which         --
-- `Core`'s `coercion-only-closes` proves at every grade. Each instance --
-- shows the converse failing, and what a coercion costs there:         --
-- forgotten time at the lower bounds, spent lease at the upper, a      --
-- dropped floor at the windows, and at the coverage order the          --
-- *operation* the box demanded, traded for the tick it took.           --
--                                                                     --
-- The two subset floors are the ones the calculus fits worst. Every    --
-- computation's grade there is the singleton of its run, and           --
-- `no-common-grade` -- proved, not decided -- shows that no grade      --
-- whatever types a conditional whose branches perform different        --
-- operations. What `if` still does at every grade is branch over       --
-- *data*, both branches making the same run.                           --
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
