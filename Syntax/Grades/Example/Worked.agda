------------------------------------------------------------------------
-- Worked instances of the example grades and grade systems.          --
--                                                                    --
-- `Grades.Example` gives the constructions; this subtree             --
-- instantiates them at one alphabet and exhibits, as checked Agda    --
-- terms, the orderings between grades and the action of each grade   --
-- morphism on them. `Typing` writes example computations in a        --
-- language over that alphabet and types them at these grades; the    --
-- type-inference examples use the same language.                     --
--                                                                    --
-- The alphabet is a sensor node: `read` a sensor (1 tick), `write` a --
-- reading to local memory (2–3), `send` one over the radio (4–6).    --
-- Its runs are `poll` (a read), `logged` (read then write), `uplink` --
-- (read, idle two ticks, send), which takes at most 9 ticks,         --
-- `logged-uplink`, `chatty-uplink` and `idle`.                       --
--                                                                    --
-- Positive and negative claims are both discharged by running the    --
-- relevant decision procedure, and the tables in the module headers  --
-- are checked.                                                       --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked where

-- The alphabet, its execution times, and the runs the examples use.

import Syntax.Grades.Example.Worked.Operations

-- What each operation touches and draws besides time: a security
-- level and an amount of energy.

import Syntax.Grades.Example.Worked.Operations.Footprint

-- Orderings and products in the three interval grades: the direction
-- of weakening in each, and the incomparable windows.

import Syntax.Grades.Example.Worked.Time

-- The two-point security level and taint sets over `Fin 3`.

import Syntax.Grades.Example.Worked.SecurityLevel

-- Left- and right-sided time with a security level, and right-sided
-- time with an energy budget.

import Syntax.Grades.Example.Worked.Product

-- A language specification over the alphabet, at which the trace-based
-- grade systems are instantiated.

import Syntax.Grades.Example.Worked.Spec

-- The grade morphisms, computed on the node's own grades, and their
-- monotonicity carrying the orderings above across.

import Syntax.Grades.Example.Worked.System

-- The trace grades: a floor, a cap and their pairing at the
-- cost-sensitive orders, and a cap at the subset order, each read as an
-- effect grade and as a resource grade; the regular cap; and the rigid
-- regular, finite-expression and regular-expression grades.

import Syntax.Grades.Example.Worked.Traces

-- Quotas and certain counts on the three operations.

import Syntax.Grades.Example.Worked.Counts

-- Flow-sensitive levels and windowed schedules, semidirect products;
-- resource levels; and mode-switch costs and mode times, mode
-- matrices.

import Syntax.Grades.Example.Worked.SemiDirect.FlowLevels
import Syntax.Grades.Example.Worked.SemiDirect.WindowedSchedules
import Syntax.Grades.Example.Worked.SemiDirect.ResourceLevels
import Syntax.Grades.Example.Worked.SemiDirect.ModeSwitchCosts
import Syntax.Grades.Example.Worked.SemiDirect.ModeTimes

-- Example computations typed against these grades and grade systems:
-- what each grade lets a program do, and what it refuses.

import Syntax.Grades.Example.Worked.Typing
