------------------------------------------------------------------------
-- Worked instances of the trace grades, following the grid of         --
-- `Grades.Example.Traces`.                                             --
--                                                                     --
-- One module per order lifted:                                        --
--                                                                     --
--   Inclusion       a run matches by being listed                     --
--   Subtrace        the lenient sub-trace order                       --
--   SubtraceTimed   its time-strict restriction                       --
--                                                                     --
-- and, inside each of the latter two, one submodule per lift, each     --
-- with its `LeftSided`, `RightSided` and `TwoSided` rows.             --
--                                                                     --
-- `Alternatives` then cuts across both: since the three lifts agree on --
-- singleton grades, it is only sets listing alternatives that separate --
-- them, and it puts the same such sets through all six lifted grades   --
-- at once, one table per scenario.                                    --
--                                                                     --
-- Every claim is closed by `holds` or `fails`, which run the grade's   --
-- own decision procedure, so the tables here are checked rather than   --
-- annotated -- a claim asserted the wrong way round does not           --
-- typecheck. Where two grades disagree, the claim is stated against    --
-- both, so the disagreement is decided from both sides.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces where

-- matched by being it: no execution times are read

import Syntax.Grades.Example.Worked.Traces.Inclusion

-- matched by being covered, time banked across the whole run

import Syntax.Grades.Example.Worked.Traces.Subtrace

-- matched by being covered window by window

import Syntax.Grades.Example.Worked.Traces.SubtraceTimed

-- both axes at once, on sets that list alternatives

import Syntax.Grades.Example.Worked.Traces.Alternatives
