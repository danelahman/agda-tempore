------------------------------------------------------------------------
-- Worked instances of the example grade algebras and grade systems.  --
--                                                                    --
-- `Grades.Examples` gives the constructions; this subtree            --
-- instantiates them at one alphabet and exhibits, as checked Agda    --
-- terms, the orderings between grades and the action of each grade   --
-- algebra morphism on them. The typing examples of the monomorphic   --
-- calculus write computations in a language over that alphabet and   --
-- type them at these grades; the type inference examples use the     --
-- same language.                                                     --
--                                                                    --
-- The alphabet is a sensor node: `read` a sensor (1 tick), `write` a --
-- reading to local memory (2–3), `send` one over the radio (4–6).    --
-- Its runs are `poll` (a read), `logged` (read then write), `uplink` --
-- (read, idle two ticks, send), which takes at most 9 ticks,         --
-- `logged-uplink`, `chatty-uplink` and `pause`.                      --
--                                                                    --
-- Positive and negative claims are both discharged by running the    --
-- relevant decision procedure, and the tables in the module headers  --
-- are checked.                                                       --
------------------------------------------------------------------------

module Grades.Examples.Worked where

-- The alphabet, its running times, and the runs the examples use.

import Grades.Examples.Worked.Operations

-- What each operation touches and draws besides time: a level of the
-- lattice and an amount of energy.

import Grades.Examples.Worked.Operations.Footprint

-- Orderings and products in time lower bounds, time upper bounds and
-- time intervals: the direction of weakening in each, and the
-- incomparable intervals.

import Grades.Examples.Worked.Time

-- The two-point lattice and taint sets over `Fin 3`.

import Grades.Examples.Worked.Lattice

-- Lower and upper bounds on time with a lattice, and upper
-- bounds on time with an energy budget.

import Grades.Examples.Worked.Product

-- The grade algebra morphisms, computed on the node's own grades, and
-- their monotonicity carrying the orderings above across.

import Grades.Examples.Worked.System

-- The trace grades: a floor, a cap and their pairing at the
-- cost-sensitive orders, and the finite run set cap, each read as an
-- effect grade and as a resource grade; the regular cap; and the timed
-- regex grades in whole steps, finite, and rational.

import Grades.Examples.Worked.Traces

-- At-most counts and at-least counts on the three operations.

import Grades.Examples.Worked.Counts

-- Flow-sensitive levels and call-time sets, semidirect products;
-- the watermark grades, defined directly; and mode-switch costs and
-- mode times, mode matrices.

import Grades.Examples.Worked.SemiDirect.FlowSensitiveLevels
import Grades.Examples.Worked.SemiDirect.CallTimeSets
import Grades.Examples.Worked.Watermarks
import Grades.Examples.Worked.Modes.SwitchCosts
import Grades.Examples.Worked.Modes.Times

-- The inter-arrival grades in rational time: the unit not least, the
-- product not commutative, a loop invariant from a closure, and a
-- resource for exactly two calls a bounded time apart.

import Grades.Examples.Worked.InterArrival
