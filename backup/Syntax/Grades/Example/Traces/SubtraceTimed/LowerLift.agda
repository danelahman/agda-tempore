------------------------------------------------------------------------
-- Sets of timed traces compared by the Hoare lower lift of           --
-- the time-strict sub-trace order.                                   --
--                                                                    --
-- `Example.Traces.Lifted.LowerLift` at that order.                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift where

-- a floor: what must have happened

import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.LeftSided

-- a cap: what may have happened

import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift.TwoSided
