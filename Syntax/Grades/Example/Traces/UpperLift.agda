------------------------------------------------------------------------
-- Sets of timed traces compared by the Smyth upper lift of the        --
-- sub-trace preorder.                                                 --
--                                                                     --
-- `LowerLift` with the quantifier over the other set: where that       --
-- family asks every trace on one side to be covered somewhere on the   --
-- other, this one asks every trace on the other side to be justified   --
-- back. Both orient `_≼_` the same way, so this is the "must" reading  --
-- against `LowerLift`'s "may", not a bound in the opposite direction.  --
--                                                                     --
--   LeftSided    a floor:  traces Q ≽ˢ traces P                       --
--   RightSided   a cap:    traces P ≽ˢ traces Q                       --
--   TwoSided     a pair of both, compared endpoint by endpoint         --
--                                                                     --
-- As in every column, the two one-sided grades are one comparison with --
-- the sets exchanged, and the two-sided one compares its endpoints in  --
-- opposite argument orders.                                           --
--                                                                     --
-- `Convex` is this family conjoined with `LowerLift`, one column per   --
-- half; on singleton grades all three agree.                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.UpperLift where

-- a floor: what must have happened, read disjunctively

import Syntax.Grades.Example.Traces.UpperLift.LeftSided

-- a cap: what may have happened, every allowance justified

import Syntax.Grades.Example.Traces.UpperLift.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.UpperLift.TwoSided
