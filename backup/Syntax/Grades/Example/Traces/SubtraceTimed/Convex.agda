------------------------------------------------------------------------
-- Sets of timed traces compared by the convex (Egli-Milner) lift of  --
-- the time-strict sub-trace order.                                   --
--                                                                    --
-- `Example.Traces.Lifted.Convex` at that order.                      --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.SubtraceTimed.Convex where

-- a floor, with every listed demand achievable by one already present

import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.LeftSided

-- a cap, with every listed allowance realised by one already present

import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.SubtraceTimed.Convex.TwoSided
