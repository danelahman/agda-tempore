------------------------------------------------------------------
-- Inference at work                                              --
--                                                                --
-- Set 1 is nine functions of the prototype's standard library.   --
-- Over an arbitrary language, inference answers `typed` for each --
-- (a theorem); at four grades, the scheme it reports is checked  --
-- by `refl`. The four grades cover the two properties the solver --
-- reads from a grade, `u-least?` and `·-comm?`.                  --
--                                                                --
-- Set 2 is annotated programs: one per annotation form, with the --
-- type it forces, and a typable handler inference is stuck on    --
-- without an annotation and types with one.                      --
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

-- Their verdicts at each grade

import TypeInference.Examples.Annotations.Time.RightSided
import TypeInference.Examples.Annotations.Time.LeftSided
import TypeInference.Examples.Annotations.Traces.Timed.RightSided
import TypeInference.Examples.Annotations.Traces.Timed.LeftSided
