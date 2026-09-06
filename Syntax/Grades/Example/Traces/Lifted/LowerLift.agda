------------------------------------------------------------------------
-- Sets of timed traces compared by the Hoare lower lift of a trace    --
-- order `_≼_`.                                                        --
--                                                                     --
-- `Inclusion` relaxed by `_≼_`: where that family asks a run to be     --
-- literally one of those listed, this one asks only that it be         --
-- covered by one.                                                     --
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

module Syntax.Grades.Example.Traces.Lifted.LowerLift where

-- a floor: what must have happened

import Syntax.Grades.Example.Traces.Lifted.LowerLift.LeftSided

-- a cap: what may have happened

import Syntax.Grades.Example.Traces.Lifted.LowerLift.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.Lifted.LowerLift.TwoSided
