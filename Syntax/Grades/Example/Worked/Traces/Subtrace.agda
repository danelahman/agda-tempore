------------------------------------------------------------------------
-- Worked instances of the trace grades over the lenient sub-trace     --
-- order, one module per lift.                                         --
--                                                                     --
-- Each lift is built the same way -- the cap compares the two sets in  --
-- the order written, the floor compares them exchanged, and the pair   --
-- uses one comparison per endpoint in those opposite directions -- so  --
-- the three modules run in parallel, and what changes between them is  --
-- only which set the quantifier runs over.                            --
--                                                                     --
-- The lifts agree on singleton grades and part company as soon as      --
-- either side lists alternatives; `UpperLift` states those             --
-- disagreements against both lifts at once, so each is checked from    --
-- both sides rather than asserted.                                    --
--                                                                     --
-- `Worked.Traces.SubtraceTimed` is the same three modules over the     --
-- time-strict order, where a further axis is in play: not only which   --
-- set is quantified over, but whether a run may bank time across a     --
-- matched operation.                                                  --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.Subtrace where

-- matched by being covered, at the operations' execution times

import Syntax.Grades.Example.Worked.Traces.Subtrace.LowerLift

-- the same, quantified over the other set of the pair

import Syntax.Grades.Example.Worked.Traces.Subtrace.UpperLift

-- both of the two above at once

import Syntax.Grades.Example.Worked.Traces.Subtrace.Convex
