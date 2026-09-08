------------------------------------------------------------------------
-- Sets of timed traces compared by the Smyth upper lift of           --
-- the time-strict sub-trace order.                                   --
--                                                                    --
-- `Example.Traces.Lifted.UpperLift` at that order.                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift where

-- a floor: what must have happened, read disjunctively

import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.LeftSided

-- a cap: what may have happened, every allowance justified

import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift.TwoSided
