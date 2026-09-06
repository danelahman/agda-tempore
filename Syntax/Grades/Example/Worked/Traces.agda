------------------------------------------------------------------------
-- Worked instances of the trace grades, one module per column of the  --
-- `Traces` grid.                                                       --
--                                                                     --
-- Each column is built the same way -- the cap compares the two sets   --
-- in the order written, the floor compares them exchanged, and the     --
-- pair uses one comparison per endpoint in those opposite directions   --
-- -- so the four modules run in parallel, and what changes between     --
-- them is only how a listed run is matched.                           --
--                                                                     --
-- The two sub-trace columns agree on singleton grades and part company --
-- as soon as either side lists alternatives; `UpperLift` states those  --
-- disagreements against both orders at once, so each is checked from   --
-- both sides rather than asserted.                                     --
--                                                                     --
-- Every claim is closed by `holds` or `fails`, which run the grade's   --
-- own decision procedure, so the tables here are checked rather than   --
-- annotated.                                                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces where

-- matched by being it: no execution times are read

import Syntax.Grades.Example.Worked.Traces.Inclusion

-- matched by being covered, at the operations' execution times

import Syntax.Grades.Example.Worked.Traces.LowerLift

-- the same, quantified over the other set of the pair

import Syntax.Grades.Example.Worked.Traces.UpperLift

-- both of the two above at once

import Syntax.Grades.Example.Worked.Traces.Convex
