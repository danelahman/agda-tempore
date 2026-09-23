------------------------------------------------------------------------
-- Completeness checks.                                                --
--                                                                     --
-- Inference checked against open derivations of pairs of constructs,  --
-- and of `tempore-lang`'s example programs: each entry pairs a        --
-- derivation of the open calculus with what `infer!` answers on its   --
-- erasure.                                                            --
------------------------------------------------------------------------

module TypeInference.SolverImpl.Demo.Completeness where

-- The derivations, the clause families and the check, over any
-- specification.

import TypeInference.SolverImpl.Demo.Completeness.Generic

-- The sensor node's windows, with the prototype's `time-lower-bound`
-- and `time-interval` programs.

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals

-- Deadlines, with the prototype's `time-upper-bound` programs.

import TypeInference.SolverImpl.Demo.Completeness.Deadlines

-- Timed traces.

import TypeInference.SolverImpl.Demo.Completeness.TimedTraces
