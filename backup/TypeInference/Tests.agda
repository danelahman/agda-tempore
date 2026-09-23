------------------------------------------------------------------------
-- Tests.                                                              --
--                                                                     --
-- Inference checked against open derivations of pairs of constructs,  --
-- and of `tempore-lang`'s example programs: each test pairs a         --
-- derivation of the open calculus with the report `reportOf` gives    --
-- on its erasure, written out in full, or with its refusal.           --
------------------------------------------------------------------------

module TypeInference.Tests where

-- The derivations, the clause families and the outcomes, over any
-- specification.

import TypeInference.Tests.Generic

-- The sensor node's windows, with the prototype's `time-lower-bound`
-- and `time-interval` programs.

import TypeInference.Tests.TimeIntervals

-- Deadlines, with the prototype's `time-upper-bound` programs.

import TypeInference.Tests.Deadlines

-- Timed traces.

import TypeInference.Tests.TimedTraces
