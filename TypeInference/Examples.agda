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
-- Set 3 is handlers with no annotation. Two leave unknowns local --
-- to the clause in cycles, which `Localise` identifies, and      --
-- inference types them at the four grades.                       --
-- Two are typable at some grades only: one drops its             --
-- continuation, one resumes it twice. Inference types each where --
-- it is typable and refutes it elsewhere.                        --
--                                                                --
-- Set 4 is boxes and delays: claims made early, on time and      --
-- late, after operations, in branches and in a handler clause,   --
-- with the box's grade given or inferred; and a box escaping     --
-- through `return` and claimed out of time, refuted through the  --
-- ordering its two bounds entail.                                --
--                                                                --
-- Set 5 is a grade of two components, time paired with a         --
-- security level, at both sides of time: a box is an embargoed   --
-- report or a session token, refused for being out of time or    --
-- for being tainted, and the schemes carry both components.      --
--                                                                --
-- Set 6 is two schemes the report simplifies: a var-rule         --
-- disjunction entailed by another, and a product with the top    --
-- absorbed. Both simplifications happen where the unit is least, --
-- so they are checked at the right-sided grades only.            --
--                                                                --
-- Set 7 is stage-level tests: solver stages called directly on   --
-- hand-written constraints, each answer checked by `refl`. They  --
-- guard steps that no program in the sets above depends on, or   --
-- depends on only in part.                                       --
------------------------------------------------------------------

module TypeInference.Examples where

-- What a scheme is, and notation for writing one

import TypeInference.Examples.Scheme
import TypeInference.Examples.Variables

-- The languages the examples run in

import TypeInference.Examples.Specs

-- The standard library: the generic module and its instances

import TypeInference.Examples.Stdlib.All

-- Annotations: the generic module and its instances

import TypeInference.Examples.Annotations.All

-- Handlers: the generic module and its instances

import TypeInference.Examples.Handlers.All

-- Boxes: the generic module and its instances

import TypeInference.Examples.Boxes.All

-- A grade of two components: the generic module and its instances

import TypeInference.Examples.Product.All

-- Report simplification: the generic module and its instances

import TypeInference.Examples.Reports.All

-- Solver stages on hand-written constraints

import TypeInference.Examples.Stages.All
