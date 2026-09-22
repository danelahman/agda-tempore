------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records which runs a computation may have. The families     --
-- differ in what the comparison between one run and one listed trace  --
-- is allowed to do:                                                   --
--                                                                     --
--   Timed.*    the two cost-sensitive orders on traces. Going up the  --
--              allowance order an operation turns into a delay long   --
--              enough to cover it; going up the coverage order a run  --
--              may do more than it was asked for.                     --
--                                                                     --
--   Subsets.*  equality. Nothing is approximated: a run either is a   --
--              listed trace or it is not, and the lift is subset      --
--              inclusion.                                             --
--                                                                     --
-- `Timed.*` has a floor, a cap and their pairing:                     --
--                                                                     --
--   Timed.LeftSided   a lower bound on what happened, cut down to     --
--                     the antichain of its weakest guarantees         --
--   Timed.RightSided  an upper bound                                  --
--   Timed.TwoSided    both at once, with a coherence field            --
--                                                                     --
-- `Subsets.*` keeps the cap, `Subsets.RightSided`.                    --
--                                                                     --
-- Every endpoint is read *disjunctively* -- one listed trace carries  --
-- the grade -- so they weaken by gaining members and the union of     --
-- two grades is their join, which is what a branching construct       --
-- wants.                                                              --
--                                                                     --
-- The `Timed.*` grades are `Traces.Lifted.*` instantiated at a trace  --
-- order; the `Subsets.*` one is built directly on `Sets`' `_⊑_`,      --
-- the discrete order not being a `TraceOrder` (it has no `≼-nil`).    --
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
-- The comparison is equality, so the cap is plain subset inclusion
-- `X ⊆ Q`: every run a computation may have is one of the traces the
-- grade lists.

import Syntax.Grades.Example.Traces.Subsets.Base
import Syntax.Grades.Example.Traces.Subsets.RightSided
