------------------------------------------------------------------------
-- Worked instances of the example grades and grade systems.           --
--                                                                     --
-- `Grades.Example` gives the constructions; this subtree instantiates  --
-- them all at one fixed alphabet and exhibits, as checked Agda terms,  --
-- which orderings hold between which grades and what each grade        --
-- morphism does to them. `Typing` then writes example computations in  --
-- a language over that alphabet and types them against these grades,   --
-- so that what a grade permits a program to do is settled by whether   --
-- the program typechecks. Nothing here is used elsewhere -- it is a    --
-- reader's tour of the grade layer.                                    --
--                                                                     --
-- The alphabet is a sensor node: `read` a sensor (1 tick), `write` a   --
-- reading to local memory (2-3), `send` one over the radio (4-6). Its  --
-- runs are `poll` (just a read), `logged` (read then write), and       --
-- `uplink` (read, idle two ticks, send), which takes 9 ticks at worst, --
-- together with `logged-uplink`, `chatty-uplink` and `idle`.           --
--                                                                     --
-- Positive and negative claims are both discharged by *running* the    --
-- relevant decision procedure, so an example asserted the wrong way    --
-- round does not typecheck. The tables in the module headers are       --
-- therefore checked, not annotations.                                  --
--                                                                     --
-- Four findings the trace examples pin down are worth having in        --
-- advance:                                                             --
--                                                                     --
--   * A bound's operations are permissions and its delays are budget.  --
--     Time buys any work that costs no more -- `⌈ write ⌉` stays       --
--     within `⟨ 3 ⟩` -- and a permitted operation buys no time, so     --
--     `⟨ 3 ⟩` does not stay within `⌈ write ⌉`. See                    --
--     `Traces.Allowance`.                                              --
--                                                                     --
--   * Read as a resource grade, such a bound is a permit that          --
--     *expires*: `unbox`'s premise `ρ' ≾ᵣ ρ` asks what elapsed to be   --
--     still within what the box allows, so overspending closes the     --
--     box rather than opening it. See the same module.                 --
--                                                                     --
--   * A guarantee is sensitive to the opposite thing, so it takes the  --
--     other order: extra work keeps a guarantee (`⌈ read ⌉` is still   --
--     covered by `⌈ read ⌉ ∙ ⌈ write ⌉`) and breaks an allowance. That --
--     is why the two endpoints of a two-sided grade cannot share one   --
--     order. See `Traces.Coverage` and `Traces.Timed.TwoSided`.        --
--                                                                     --
--   * With equality as the comparison there is nothing left for the    --
--     two endpoints to differ about, and the disjunctive floor         --
--     condition collapses onto the cap's. So the subset floor is read  --
--     conjunctively instead -- every listed run separately demanded -- --
--     which weakens by losing members and needs a branching rule that  --
--     unions its branches' grades rather than coercing both to one.    --
--     See `Traces.Subsets.LeftSided`.                                  --
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
