------------------------------------------------------------------------
-- Worked instances of the trace grades, one module per column of the  --
-- `Traces` grid.                                                       --
--                                                                     --
-- Each column is built the same way -- the cap compares the two sets   --
-- in the order written, the floor compares them exchanged, and the     --
-- pair uses one comparison per endpoint in those opposite directions   --
-- -- so the three modules run in parallel, and what changes between    --
-- them is only how a listed run is matched.                           --
--                                                                     --
-- Every claim is closed by `holds` or `fails`, which run the grade's   --
-- own decision procedure, so the tables here are checked rather than   --
-- annotated.                                                          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces where

-- matched by being it: no execution times are read

import Syntax.Grades.Example.Worked.Traces.Inclusion

-- matched by being covered, at the operations' execution times

import Syntax.Grades.Example.Worked.Traces.Subtrace

-- as above, and matched back again

import Syntax.Grades.Example.Worked.Traces.Convex
