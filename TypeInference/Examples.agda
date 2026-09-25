------------------------------------------------------------------
-- Inference at work                                              --
--                                                                --
-- Set 1 is nine functions of the prototype's standard library.   --
-- Over an arbitrary language, inference answers `typed` for each --
-- (a theorem); at four grades, the scheme it reports is checked  --
-- by `refl`. The four grades cover the two properties the solver --
-- reads from a grade, `u-least?` and `·-comm?`.                  --
------------------------------------------------------------------

module TypeInference.Examples where

-- What a report is, and notation for writing one

import TypeInference.Examples.Report
import TypeInference.Examples.Variables

-- The languages the examples run in

import TypeInference.Examples.Specs

-- The standard library: the programs, the theorem, the shared schemes

import TypeInference.Examples.Stdlib

-- The schemes at each grade

import TypeInference.Examples.Stdlib.Time.RightSided
import TypeInference.Examples.Stdlib.Time.LeftSided
import TypeInference.Examples.Stdlib.Traces.Timed.RightSided
import TypeInference.Examples.Stdlib.Traces.Timed.LeftSided
