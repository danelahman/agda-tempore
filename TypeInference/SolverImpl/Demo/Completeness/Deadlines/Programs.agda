--------------------------------------------------------------------------------
-- Completeness checks at deadlines: programs of `tempore-lang`'s examples.   --
--                                                                            --
-- The prototype's `time-upper-bound` programs, read at these deadlines:      --
-- `Get` is `read`, `Tick` is `write`, integers are readings when an          --
-- operation's arity asks for one and `Bool` where they must be eternal, and  --
-- arithmetic keeps one operand.                                              --
--------------------------------------------------------------------------------

module TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs where

-- `time_upper.tpe`

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.TimeUpper

-- `handlers_upper_bound.tpe`

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.HandlersUpperBound

-- `eternal_types.tpe`, and its `after` apart

import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.EternalTypes
import TypeInference.SolverImpl.Demo.Completeness.Deadlines.Programs.After
