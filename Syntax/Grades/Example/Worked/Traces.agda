------------------------------------------------------------------------
-- Worked instances of the trace grades.                               --
--                                                                     --
-- One module per grade. Each is worked out twice over: once as an      --
-- effect grade, where `coerce` moves along the order, and once as a    --
-- resource grade, where `unbox` discharges its premise against it.     --
--                                                                     --
-- Every run is written out in full in every claim, and every claim is  --
-- closed by running the grade's own decision procedure, so the tables  --
-- are checked rather than annotated.                                   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces where

-- sets of traces as guarantees, at the coverage order

import Syntax.Grades.Example.Worked.Traces.Coverage

-- sets of traces as upper bounds, at the allowance order

import Syntax.Grades.Example.Worked.Traces.Allowance

-- and both at once, each endpoint at its own order

import Syntax.Grades.Example.Worked.Traces.TwoSided
