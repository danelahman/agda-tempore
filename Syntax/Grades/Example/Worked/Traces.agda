------------------------------------------------------------------------
-- Worked instances of the trace grades.                               --
--                                                                     --
-- One module per order the grade of upper bounds is taken at, as the   --
-- trace family is rebuilt. Each works the grade out twice over: once   --
-- as an effect grade, where `coerce` moves along the order, and once   --
-- as a resource grade, where `unbox` discharges its premise against    --
-- it.                                                                  --
--                                                                     --
-- `Allowance` is about what a bound says -- its operations permit and  --
-- its delays are budget -- and `AllowanceTimed` about where it says    --
-- it, budget being local to the segment the bound places it in.        --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure, so the tables  --
-- are checked rather than annotated.                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces where

-- sets of traces as upper bounds, at the allowance order

import Syntax.Grades.Example.Worked.Traces.Allowance

-- the same, at its time-strict restriction

import Syntax.Grades.Example.Worked.Traces.AllowanceTimed
