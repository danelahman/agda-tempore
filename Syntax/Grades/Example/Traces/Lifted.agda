------------------------------------------------------------------------
-- The trace-grade grid, built over an arbitrary trace order.          --
--                                                                     --
-- Every grade below takes a `Traces.Order.TraceOrder` as a parameter   --
-- and lifts its comparison `_≼_` to sets of traces. Nothing here       --
-- inspects that order, so the grid is built once and instantiated:     --
--                                                                     --
--   Example.Traces.Subtrace        the lenient sub-trace order        --
--   Example.Traces.SubtraceTimed   its time-strict restriction        --
--                                                                     --
-- The columns are the three lifts of the order --                     --
--                                                                     --
--   LowerLift   Hoare:       every trace on the left matched right     --
--   UpperLift   Smyth:       every trace on the right matched left     --
--   Convex      Egli-Milner: both at once                             --
--                                                                     --
-- and the rows are the sidedness, as in `Example.Time`: a floor, a     --
-- cap, or a pair of endpoints.                                        --
--                                                                     --
-- `Example.Traces.Inclusion` is the same grid at `_≡_`, which is not   --
-- a `TraceOrder` -- `ε ≡ t` fails -- and so stands outside the axis.   --
------------------------------------------------------------------------

module Syntax.Grades.Example.Traces.Lifted where

import Syntax.Grades.Example.Traces.Lifted.LowerLift
import Syntax.Grades.Example.Traces.Lifted.UpperLift
import Syntax.Grades.Example.Traces.Lifted.Convex
