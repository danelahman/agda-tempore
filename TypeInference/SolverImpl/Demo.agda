------------------------------------------------------------------------
-- The solver, run on example programs.                                --
--                                                                     --
-- `TypeInference.SolverImpl` is parametric in a language              --
-- specification, in an enumeration of its operations, and in two      --
-- optional proofs that a unit is least. A demo fixes all of that and  --
-- states, as equations discharged by `refl`, what the solver then     --
-- infers -- so an example asserted the wrong way round does not       --
-- typecheck.                                                          --
--                                                                     --
-- `Generic` holds what the demos are written with, over an arbitrary  --
-- specification: the library-shaped programs, which name no grade,    --
-- and the wrappers that run the solver and measure its output. Each   --
-- instance below supplies its own grades and writes its own results   --
-- out, since against an abstract specification nothing computes.      --
------------------------------------------------------------------------

module TypeInference.SolverImpl.Demo where

-- The programs and the measurement helpers, over any specification.

import TypeInference.SolverImpl.Demo.Generic

-- Two-sided time windows as effect grades, lower bounds on elapsed
-- time as resource grades, projected onto each other by keeping a
-- window's lower endpoint: the suite covering every raw-term former,
-- what these grades do, and what the solver's passes do with them. A
-- second specification, deadlines, closes it -- the same operations
-- graded so that the unit *is* least, which is what a handler needs.

import TypeInference.SolverImpl.Demo.TimeIntervals

-- Finite sets of timed runs as both effect and resource grades, read
-- as allowances and ordered by what they permit, over an identity
-- grade system: the same coverage, and what these grades say that a
-- window cannot -- a branch graded by the union of its arms' runs, a
-- sequence by the run it makes, a claim on a boxed resource refused
-- for doing the right things in the wrong order. Their unit is least,
-- so the handler `TimeIntervals` declines is inferred here.

import TypeInference.SolverImpl.Demo.TimedTraces

-- Inference checked against open derivations of pairs of constructs,
-- and of `tempore-lang`'s example programs, at the demos' grades.

import TypeInference.SolverImpl.Demo.Completeness
