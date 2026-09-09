------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records which runs a computation may have. There are three,  --
-- built over the two orders on traces:                                --
--                                                                     --
--   Coverage.LeftSided    a floor: whatever happened, it covered one   --
--                         of the listed traces                        --
--   Allowance.RightSided  a cap: whatever happened, it stayed within   --
--                         one of them                                 --
--   TwoSided              both at once                                --
--                                                                     --
-- Every set is read *disjunctively*, at either endpoint -- one listed  --
-- trace carries it -- so every endpoint weakens by gaining members and --
-- the union of two grades is their join. That is what a branching      --
-- construct would need, and it is why the floor is lifted the way it   --
-- is rather than conjunctively.                                       --
--                                                                     --
-- The two endpoints take different orders and must: a guarantee wants  --
-- one in which time never buys an operation, an allowance one in which --
-- a listed delay is a budget that buys them. The constructions in      --
-- `Traces.Lifted.*` are over an arbitrary order, or an arbitrary pair  --
-- of them, and the modules beside them instantiate.                    --
--                                                                     --
-- The earlier grid -- four lifts against three sidednesses over the    --
-- sub-trace orders -- is parked under `backup/`.                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

-- the constructions, over an arbitrary order (or pair of orders)

import Syntax.Grades.Example.Traces.Lifted.LeftSided
import Syntax.Grades.Example.Traces.Lifted.RightSided
import Syntax.Grades.Example.Traces.Lifted.TwoSided

-- guarantees, at the coverage order

import Syntax.Grades.Example.Traces.Coverage.LeftSided

-- allowances, at the allowance order

import Syntax.Grades.Example.Traces.Allowance.RightSided

-- and both at once

import Syntax.Grades.Example.Traces.TwoSided
