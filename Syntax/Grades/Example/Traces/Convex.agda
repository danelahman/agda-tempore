------------------------------------------------------------------------
-- Sets of timed traces compared by the convex (Egli-Milner) lift of   --
-- the sub-trace preorder.                                             --
--                                                                     --
-- Each grade of `Subtrace` strengthened by the Smyth partner of its    --
-- comparison: as well as every trace on one side being matched on the  --
-- other, every trace on the other side must be matched back. Weakening --
-- may therefore fill in between the listed alternatives but not extend --
-- past them -- the extremes are exact.                                --
--                                                                     --
--   LeftSided    a floor, convexly compared                           --
--   RightSided   a cap, convexly compared                             --
--   TwoSided     a pair of both, compared endpoint by endpoint         --
--                                                                     --
-- The two halves of each comparison orient `_≼_` the same way and      --
-- differ in which set the quantifier runs over, so -- unlike the       --
-- floor/cap distinction -- the convex strengthening is visible even at --
-- `_≡_`, where it would collapse the order to set equality.           --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.Convex where

-- a floor, with every listed demand achievable by one already present

import Syntax.Grades.Example.Traces.Convex.LeftSided

-- a cap, with every listed allowance realised by one already present

import Syntax.Grades.Example.Traces.Convex.RightSided

-- both at once, as a pair of endpoints

import Syntax.Grades.Example.Traces.Convex.TwoSided
