------------------------------------------------------------------------
-- Worked instances of the example grades and grade systems.           --
--                                                                     --
-- `Grades.Example` gives the constructions; this subtree instantiates --
-- them all at one fixed alphabet and exhibits, as checked Agda terms, --
-- which orderings hold between which grades and what each grade       --
-- morphism does to them. `Typing` then writes example computations in --
-- a language over that alphabet and types them against these grades.  --
-- Nothing here is used elsewhere -- it is a reader's tour of the      --
-- grade layer.                                                        --
--                                                                     --
-- The alphabet is a sensor node: `read` a sensor (1 tick), `write` a  --
-- reading to local memory (2-3), `send` one over the radio (4-6). Its --
-- runs are `poll` (just a read), `logged` (read then write), and      --
-- `uplink` (read, idle two ticks, send), which takes 9 ticks at       --
-- worst, together with `logged-uplink`, `chatty-uplink` and `idle`.   --
--                                                                     --
-- Positive and negative claims are both discharged by running the     --
-- relevant decision procedure, so an example asserted the wrong way   --
-- round does not typecheck. The tables in the module headers are      --
-- therefore checked, not annotations.                                 --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked where

-- The alphabet, its execution times, and the runs the examples use.

import Syntax.Grades.Example.Worked.Operations

-- Orderings and products in the four interval grades: which way
-- weakening points in each, and which windows are incomparable.

import Syntax.Grades.Example.Worked.Time

-- A language specification over the alphabet, which the trace-based
-- grade systems need in order to be instantiated.

import Syntax.Grades.Example.Worked.Spec

-- The grade morphisms, computed on the node's own grades, and their
-- monotonicity carrying the orderings above across.

import Syntax.Grades.Example.Worked.Systems

-- The six trace grades -- a floor, a cap and their pairing, at the
-- cost-sensitive orders and at the subset order -- each read as an
-- effect grade and as a resource grade.

import Syntax.Grades.Example.Worked.Traces

-- Example computations typed against these grades, over identity grade
-- systems: what each grade lets a program do, and what it refuses.

import Syntax.Grades.Example.Worked.Typing
