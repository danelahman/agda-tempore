------------------------------------------------------------------------
-- Grades that are (non-empty) sets of timed traces.                   --
--                                                                     --
-- A grade records which runs a computation may have. At present there --
-- is one such grade, read as an upper bound:                          --
--                                                                     --
--   every run stays within one of the listed bounds                   --
--                                                                     --
-- built once in `Traces.Lifted.RightSided`, over an arbitrary order    --
-- on traces, and instantiated at `Traces.Allowance` -- where a bound's --
-- operations are permissions and its delays a budget, available only  --
-- where the bound places it.                                          --
--                                                                     --
-- The grades that read a set of traces as a *lower* bound, and the     --
-- two-sided ones that pair the two readings, are being rebuilt one at  --
-- a time; the earlier grid of them is parked under `backup/`.          --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces where

-- upper bounds over an arbitrary order on traces

import Syntax.Grades.Example.Traces.Lifted.RightSided

-- at the allowance order

import Syntax.Grades.Example.Traces.Allowance.RightSided
