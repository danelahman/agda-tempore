------------------------------------------------------------------------
-- Worked instances of the example grades and grade systems.           --
--                                                                     --
-- `Grades.Example` gives the constructions; this subtree instantiates  --
-- them all at one fixed alphabet and exhibits, as checked Agda terms,  --
-- which orderings hold between which grades and what each grade        --
-- morphism does to them. Nothing here is used elsewhere -- it is a     --
-- reader's tour of the grade layer.                                    --
--                                                                     --
-- The alphabet is a sensor node: `read` a sensor (1 tick), `write` a   --
-- reading to local memory (2-3), `send` one over the radio (4-6). Its  --
-- runs are `poll` (just a read), `logged` (read then write), and       --
-- `uplink` (read, idle two ticks, send), which takes 9 ticks at worst. --
--                                                                     --
-- Positive and negative claims are both discharged by *running* the    --
-- relevant decision procedure, so an example asserted the wrong way    --
-- round does not typecheck. The tables in the module headers are       --
-- therefore checked, not annotations.                                  --
--                                                                     --
-- Two findings the examples pin down are worth having in advance:      --
--                                                                     --
--   * Every grade order runs so that `unbox`'s premise `ρ' ≾ᵣ ρ` --    --
--     what elapsed, below what the box demands -- is discharged by     --
--     having done *more* than `ρ` asks for, and never by less. See     --
--     `TraceSets` rows 1 and 2.                                        --
--                                                                     --
--   * Time discharges a demand for an operation, at that operation's   --
--     execution time, but doing operations does not discharge a demand --
--     for time. The `uplink` run takes nine ticks, yet does not meet a --
--     demand for three ticks of waiting: its only idle time is the two --
--     ticks it actually idles for. See `TraceSets`.                    --
--                                                                     --
--   * Inclusion and the convex order are incomparable, and both sit    --
--     inside the sub-trace order. See `TraceSets` rows 1 and 4.        --
------------------------------------------------------------------------

module Syntax.Grades.Example.Worked where

-- The alphabet, its execution times, and the runs the examples use.

import Syntax.Grades.Example.Worked.Operations

-- Orderings and products in the four interval grades: which way
-- weakening points in each, and which windows are incomparable.

import Syntax.Grades.Example.Worked.Intervals

-- The trace-based interval grades, one submodule per grade: a floor
-- under what must have happened, a cap on what may have, and the pair
-- of them.

import Syntax.Grades.Example.Worked.TraceIntervals

-- The two trace-set grades that are not intervals -- inclusion and the
-- convex order -- and how they sit against the left-sided one.

import Syntax.Grades.Example.Worked.TraceSets

-- A language specification over the alphabet, which the trace-based
-- grade systems need in order to be instantiated.

import Syntax.Grades.Example.Worked.Spec

-- The four grade morphisms, computed on the node's own grades, and
-- their monotonicity carrying the orderings above across.

import Syntax.Grades.Example.Worked.Systems
