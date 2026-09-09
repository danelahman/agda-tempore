------------------------------------------------------------------------
-- Typed example computations, one grade at a time.                    --
--                                                                     --
-- The rest of this subtree exhibits orderings between grades. This one --
-- puts the grades to work: it fixes a language over the sensor node's  --
-- alphabet and writes example computations in it, each typed against a --
-- value type and an effect grade, so that what a grade permits is      --
-- settled by whether a program typechecks.                            --
--                                                                     --
-- Every instance uses an *identity* grade system -- effect grades and  --
-- resource grades are the same monoid, and `∣_∣ᵉ` is the identity --   --
-- so `mapᵉ` disappears and the rules read directly: the lock a         --
-- computation puts on the context is its own effect grade, and         --
-- `unbox`'s premise compares what a computation did with the grade on  --
-- the box. The instances then differ only in that monoid.              --
--                                                                     --
-- Each instance writes its programs out in full, at its own grades,    --
-- exercising the language's features -- operations, sequencing,        --
-- `delay`, `if`, pattern matching, functions, `box`/`unbox`, and       --
-- handlers -- with every side condition discharged where the rule      --
-- imposes it, by running the grade's own decision procedure. A program --
-- the grade refuses is not written; what stands in its place is a      --
-- refutation of the bound it would have needed. `Typing/Core.agda`     --
-- holds only what the programs are written *with*: the language, the   --
-- three ways of meeting `var`'s bound, and the operation clauses       --
-- handed to `handle`, whose typing is intricate and the same at every  --
-- grade. Reading the instances side by side, the same box is:          --
--                                                                     --
--   lower bounds       a resource that becomes available, claimable    --
--                      once enough time has passed and never too late  --
--                                                                     --
--   upper bounds       a lease, claimable at once and expiring once    --
--                      more than it allows has been spent              --
--                                                                     --
--   windows            both at once: available from one endpoint, gone --
--                      after the other                                 --
--                                                                     --
--   trace guarantees   a resource that comes due when *work* has been  --
--                      done, which idling cannot stand in for          --
--                                                                     --
--   trace allowances   a permit for particular runs, refusing a claim  --
--                      not for taking too long but for doing the wrong --
--                      thing, or the right things in the wrong order   --
--                                                                     --
--   trace contracts    both of those at once, refusing a claim for     --
--                      having done too little and for too much         --
--                                                                     --
--   demanded runs      a resource naming the run that must have        --
--                      happened, with nothing standing in for it       --
--                                                                     --
--   listed runs        a permit naming the runs it covers outright,    --
--                      where an unlisted run is refused however little --
--                      it costs                                        --
--                                                                     --
--   Egli-Milner        the two subset readings paired, which against   --
--                      this calculus behaves as the demanded-run one   --
--                                                                     --
-- Two further rules put the unit on opposite sides of the order, and   --
-- each instance settles them independently:                            --
--                                                                     --
--   `var`'s bound is `ρ ≾ᵣ uᵣ` -- is what elapsed below the unit? If   --
--   not, a non-eternal variable goes stale as soon as that much has     --
--   happened, and data that is to survive has to be boxed.              --
--                                                                     --
--   a clause that drops its continuation needs `uₑ ≾ₑ op-grade op ·ₑ   --
--   ε''` -- is the unit below the clause's grade? If not, no handler    --
--   clause may discard the computation it is handling.                  --
--                                                                     --
--                       goes stale?   may discard?                     --
--   lower bounds        no            no                                --
--   upper bounds        yes           yes                               --
--   windows             yes           no                                --
--   trace guarantees    no            no                                --
--   trace allowances    yes           yes                               --
--   trace contracts     yes           no                                --
--   demanded runs       yes           no                                --
--   listed runs         yes           no                                --
--   Egli-Milner         yes           no                                --
--                                                                     --
-- Each entry is a proof or a refutation in the instance concerned.      --
--                                                                     --
-- The two subset floors are the ones the calculus fits worst, and both --
-- say so in the same way. Every computation's grade there is the       --
-- singleton of its run, and `no-common-grade` -- proved, not decided --  --
-- shows that no grade whatever types a conditional whose branches      --
-- perform different operations. What `if` still does at every grade is --
-- branch over *data*, both branches making the same run.               --
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

-- as a cap: a box names the runs it covers outright, nothing paying for
-- anything else

import Syntax.Grades.Example.Worked.Typing.Traces.Subsets.RightSided

-- and as both, the Egli-Milner reading

import Syntax.Grades.Example.Worked.Typing.Traces.Subsets.TwoSided
