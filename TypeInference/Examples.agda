------------------------------------------------------------------
-- Inference at work                                              --
--                                                                --
-- Set 1 is nine functions of the prototype's standard library.   --
-- Over an arbitrary language, inference answers `typed` for each --
-- (a theorem); at four grades, the scheme it reports is checked  --
-- by `refl`. The four grades cover the two properties the solver --
-- reads from a grade, `u-least?` and `·-comm?`.                  --
--                                                                --
-- Set 2 is annotated programs, one per annotation form with the  --
-- type it forces.                                                --
--                                                                --
-- Set 3 is typable handlers with no annotation, whose clauses    --
-- leave unknowns local to the clause; inference types each at    --
-- the four grades.                                               --
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

-- Annotations: the programs, the theorems, the schemes

import TypeInference.Examples.Annotations

-- The schemes at each grade

import TypeInference.Examples.Annotations.Time.RightSided
import TypeInference.Examples.Annotations.Time.LeftSided
import TypeInference.Examples.Annotations.Traces.Timed.RightSided
import TypeInference.Examples.Annotations.Traces.Timed.LeftSided

-- Handlers: the programs, the typings, the schemes

import TypeInference.Examples.Handlers

-- The schemes at each grade

import TypeInference.Examples.Handlers.Time.RightSided
import TypeInference.Examples.Handlers.Time.LeftSided
import TypeInference.Examples.Handlers.Traces.Timed.RightSided
import TypeInference.Examples.Handlers.Traces.Timed.LeftSided
