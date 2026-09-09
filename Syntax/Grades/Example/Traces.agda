------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records which runs a computation may have. There are two     --
-- families of three, differing in what the comparison between one run  --
-- and one listed trace is allowed to do:                               --
--                                                                     --
--   Timed.*    the two cost-sensitive orders on traces. Going up the   --
--              allowance order an operation turns into a delay long    --
--              enough to cover it; going up the coverage order a run   --
--              may do more than it was asked for.                      --
--                                                                     --
--   Subsets.*  equality. Nothing is approximated: a run either is a    --
--              listed trace or it is not, and the lifts are the two    --
--              directions of subset inclusion.                         --
--                                                                     --
-- Each family has a floor, a cap and their pairing:                    --
--                                                                     --
--   *.LeftSided   a lower bound on what happened                       --
--   *.RightSided  an upper bound                                       --
--   *.TwoSided    both at once, with a coherence field                 --
--                                                                     --
-- HOW THE ENDPOINTS ARE READ. Five of the six endpoints are read       --
-- *disjunctively* -- one listed trace carries the grade -- so they     --
-- weaken by gaining members and the union of two grades is their join, --
-- which is what a branching construct wants. The exception is          --
-- `Subsets.LeftSided`, which is read conjunctively and weakens by      --
-- losing members. That is forced: with equality as the comparison the  --
-- disjunctive floor condition is `X ⊆ P`, which is the cap's own, so a --
-- subset floor has to be conjunctive or it is not a floor at all.      --
--                                                                     --
-- The `Timed.*` grades are `Traces.Lifted.*` instantiated at a trace   --
-- order; the `Subsets.*` ones are built directly on `Sets`' `_⊑_`,     --
-- the discrete order not being a `TraceOrder` (it has no `≼-nil`).     --
--                                                                     --
-- A grid of four lifts against three sidednesses, over the sub-trace   --
-- orders, is parked under `backup/`.                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

------------------------------------------------------------------------
-- The constructions, over an arbitrary order (or pair of orders)

import Syntax.Grades.Example.Traces.Lifted.LeftSided
import Syntax.Grades.Example.Traces.Lifted.RightSided
import Syntax.Grades.Example.Traces.Lifted.TwoSided

------------------------------------------------------------------------
-- At the cost-sensitive orders
--
-- The floor takes the coverage order and the cap the allowance order,
-- and they must differ: a guarantee wants an order in which time never
-- buys an operation, an allowance one in which a listed delay is a
-- budget that buys them.

import Syntax.Grades.Example.Traces.Timed.LeftSided
import Syntax.Grades.Example.Traces.Timed.RightSided
import Syntax.Grades.Example.Traces.Timed.TwoSided

------------------------------------------------------------------------
-- At the subset order
--
-- One relation serves both endpoints, taken in its two directions of
-- inclusion, so the two-sided grade is the plain Egli-Milner interval
-- `P ⊆ X ⊆ Q` -- and its coherence field is exactly the condition for
-- that interval to be inhabited, which the timed one cannot manage.

import Syntax.Grades.Example.Traces.Subsets.Base
import Syntax.Grades.Example.Traces.Subsets.LeftSided
import Syntax.Grades.Example.Traces.Subsets.RightSided
import Syntax.Grades.Example.Traces.Subsets.TwoSided
