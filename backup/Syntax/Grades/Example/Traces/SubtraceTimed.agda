------------------------------------------------------------------------
-- Trace grades over the time-strict sub-trace order.                 --
--                                                                    --
-- `Example.Traces.Lifted` instantiated at `Traces.SubtraceTimed`'s   --
-- `_≼ᵗ_`: as over the lenient order, the demanded operations must    --
-- occur in order and others may occur in between, but time no longer --
-- moves across a match. A delay the demand places between two of its --
-- operations must be covered by what the run does between the same   --
-- two, so a grade here constrains *when* work is done, not only how  --
-- much of it there is.                                               --
--                                                                    --
-- Since the time-strict order is a restriction of the lenient one,   --
-- every grade below is finer than its counterpart under              --
-- `Example.Traces.Subtrace`: fewer runs discharge it.                --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.SubtraceTimed where

import Syntax.Grades.Example.Traces.SubtraceTimed.LowerLift
import Syntax.Grades.Example.Traces.SubtraceTimed.UpperLift
import Syntax.Grades.Example.Traces.SubtraceTimed.Convex
import Syntax.Grades.Example.Traces.SubtraceTimed.Mixed
