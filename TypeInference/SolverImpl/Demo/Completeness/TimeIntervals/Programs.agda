--------------------------------------------------------------------------------
-- Completeness checks at the sensor node's windows: programs of              --
-- `tempore-lang`'s examples.                                                 --
--                                                                            --
-- The prototype's `time-lower-bound` and `time-interval` programs, read at   --
-- these windows and lower bounds: `Get` is `read` and `Set` is `write`,      --
-- integers are readings, a resource window `(n, m)` is its lower bound       --
-- `[ n ,+∞⟩`, arithmetic is a pair of the operands, and a two-constructor    --
-- datatype is `Bool`.                                                        --
--------------------------------------------------------------------------------

module TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs where

-- `operations.tpe`

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Operations

-- `delay.tpe`, and its `foobar` apart

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Delay
import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Foobar

-- `time_intervals.tpe`

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.TimeIntervals

-- `3dprint.tpe`

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.Print3D

-- `handlers_lower_bound.tpe`

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.HandlersLowerBound

-- `handlers_nested.tpe`

import TypeInference.SolverImpl.Demo.Completeness.TimeIntervals.Programs.HandlersNested
