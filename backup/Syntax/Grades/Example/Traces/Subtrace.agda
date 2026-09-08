------------------------------------------------------------------------
-- Trace grades over the lenient sub-trace order.                     --
--                                                                    --
-- `Example.Traces.Lifted` instantiated at `Traces.Subtrace`'s `_≼_`: --
-- a demand is met by a run that performs the demanded operations in  --
-- order -- others may occur in between -- and that spends at least   --
-- the demanded time somewhere before each delay comes due. Time is   --
-- banked globally, so a run may earn it early and spend it late.     --
--                                                                    --
-- `Example.Traces.SubtraceTimed` is the same grid over the order     --
-- that refuses that, and `Example.Traces.Inclusion` the grid at      --
-- `_≡_`, where nothing is relaxed at all.                            --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.Subtrace where

import Syntax.Grades.Example.Traces.Subtrace.LowerLift
import Syntax.Grades.Example.Traces.Subtrace.UpperLift
import Syntax.Grades.Example.Traces.Subtrace.Convex
import Syntax.Grades.Example.Traces.Subtrace.Mixed
