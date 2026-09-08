------------------------------------------------------------------------
-- Sets of timed traces bounded by a Smyth floor and a Hoare cap.      --
--                                                                     --
-- The one column of the grid that mixes the lifts, and the only one    --
-- whose two endpoints both speak about *every* run: the floor asks     --
-- each run to cover some listed demand, the cap asks each run to stay  --
-- within some listed allowance. That is what `[ min , max ]` says of a --
-- duration, so this is the trace counterpart of `Time.TwoSided`.      --
--                                                                     --
-- Having no one-sided rows of its own, the column is a single module:  --
-- its floor read alone is `UpperLift.LeftSided` and its cap read alone --
-- is `LowerLift.RightSided`, which is where the one-sided grades and   --
-- their laws already live.                                            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.Lifted.Mixed where

-- a floor and a cap, each bounding every run

import Syntax.Grades.Example.Traces.Lifted.Mixed.TwoSided
