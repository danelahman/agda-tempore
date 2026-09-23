--------------------------------------------------------------------------------
-- Tests at deadlines: programs of `tempore-lang`'s examples.                 --
--                                                                            --
-- The prototype's `time-upper-bound` programs, read at these deadlines:      --
-- `Get` is `read`, `Tick` is `write`, integers are readings when an          --
-- operation's arity asks for one and `Bool` where they must be eternal, and  --
-- arithmetic keeps one operand.                                              --
--------------------------------------------------------------------------------

module TypeInference.Tests.Deadlines.Programs where

-- `time_upper.tpe`

import TypeInference.Tests.Deadlines.Programs.TimeUpper

-- `handlers_upper_bound.tpe`

import TypeInference.Tests.Deadlines.Programs.HandlersUpperBound

-- `eternal_types.tpe`, and its `after` apart

import TypeInference.Tests.Deadlines.Programs.EternalTypes
import TypeInference.Tests.Deadlines.Programs.After
