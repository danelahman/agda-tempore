------------------------------------------------------------------------
-- Sets of timed traces compared up to the sub-trace preorder.         --
--                                                                     --
-- `Inclusion` relaxed by `_≼_`: where that family asks a run to be     --
-- literally one of those listed, this one asks only that it be         --
-- covered by one, at the operations' prescribed execution times.       --
--                                                                     --
--   LeftSided    a floor:  traces Q ≼ˢ traces P                       --
--   RightSided   a cap:    traces P ≼ˢ traces Q                       --
--   TwoSided     a pair of both, compared endpoint by endpoint         --
--                                                                     --
-- As in `Inclusion`, the two one-sided grades are one comparison with  --
-- the sets exchanged, and the two-sided one compares its endpoints in  --
-- opposite directions -- the trace analogue of                         --
-- `min i₂ ≤ min i₁ × max i₁ ≤ max i₂`.                                --
--                                                                     --
-- `Convex` strengthens each of these by the Smyth partner of its       --
-- comparison.                                                         --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.LowerLift where

-- a floor: what must have happened

import Syntax.Grades.Example.Traces.LowerLift.LeftSided

-- a cap: what may have happened

import Syntax.Grades.Example.Traces.LowerLift.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.LowerLift.TwoSided
