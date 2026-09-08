------------------------------------------------------------------------
-- Worked instances of the trace grades over the time-strict sub-trace --
-- order, one module per lift.                                         --
--                                                                     --
-- Laid out exactly as `Worked.Traces.Subtrace` is, so the two can be   --
-- read side by side. `Order` first isolates what the order itself      --
-- changes, on single traces and before any grade is built; the three   --
-- lift modules then carry that difference up to the grades.           --
--                                                                     --
-- Two axes vary independently here. Which lift is taken decides which  --
-- set the quantifier runs over; which order is lifted decides whether  --
-- a run may bank time across a matched operation. Wherever a claim     --
-- turns on either, it is stated against the neighbouring grade too --  --
-- the other lift at this order, or this lift at the lenient one -- so  --
-- the separations are decided rather than asserted.                    --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked.Traces.SubtraceTimed where

-- what the order changes, on single traces

import Syntax.Grades.Example.Worked.Traces.SubtraceTimed.Order

-- matched by being covered, window by window

import Syntax.Grades.Example.Worked.Traces.SubtraceTimed.LowerLift

-- the same, quantified over the other set of the pair

import Syntax.Grades.Example.Worked.Traces.SubtraceTimed.UpperLift

-- both of the two above at once

import Syntax.Grades.Example.Worked.Traces.SubtraceTimed.Convex

-- one of them at each endpoint, where the order's difference lands on
-- the consistency field rather than on a coercion

import Syntax.Grades.Example.Worked.Traces.SubtraceTimed.Mixed
