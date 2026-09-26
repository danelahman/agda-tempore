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
-- Set 3 is handlers with no annotation. One leaves unknowns      --
-- local to the clause, and inference types it at the four        --
-- grades.                                                        --
-- Two are typable at some grades only: one drops its             --
-- continuation, one resumes it twice. Inference types each where --
-- it is typable and refutes it elsewhere.                        --
--                                                                --
-- Set 4 is boxes and delays: claims made early, on time and      --
-- late, after operations, in branches and in a handler clause,   --
-- with the box's grade given or inferred.                        --
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

-- The verdicts and schemes at each grade

import TypeInference.Examples.Handlers.Time.RightSided
import TypeInference.Examples.Handlers.Time.LeftSided
import TypeInference.Examples.Handlers.Traces.Timed.RightSided
import TypeInference.Examples.Handlers.Traces.Timed.LeftSided

-- Boxes: the programs, the typings, the schemes

import TypeInference.Examples.Boxes

-- The verdicts and schemes at each grade

import TypeInference.Examples.Boxes.Time.RightSided
import TypeInference.Examples.Boxes.Time.LeftSided
import TypeInference.Examples.Boxes.Traces.Timed.RightSided
import TypeInference.Examples.Boxes.Traces.Timed.LeftSided
