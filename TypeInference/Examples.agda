------------------------------------------------------------------
-- Inference examples                                           --
--                                                              --
-- Set 1 consists of nine functions of the prototype's standard --
-- library. Over an arbitrary language, inference answers       --
-- `typed` for each (a theorem); at four grades, the reported   --
-- scheme is checked by `refl`. The four grades cover the       --
-- combinations of the two properties the solver reads from a   --
-- grade, `u-least?` and `·-comm?`.                             --
--                                                              --
-- Set 2 consists of annotated programs, at both annotation     --
-- forms, each with the type the annotation forces.             --
--                                                              --
-- Set 3 consists of handlers without annotations. Two leave    --
-- cycles of unknowns local to the clause, which `Localise`     --
-- identifies, and are typed at the four grades. Two are        --
-- typable at some grades only: one discards its continuation,  --
-- one resumes it twice; inference types each where it is       --
-- typable and refutes it elsewhere.                            --
--                                                              --
-- Set 4 consists of boxes and delays: claims made early, on    --
-- time and late, after operations, in branches and in a        --
-- handler clause, with the box's grade given or inferred; and  --
-- a box that escapes through `return` and is claimed out of    --
-- time, refuted through the ordering entailed by its two       --
-- bounds.                                                      --
--                                                              --
-- Set 5 is at a grade of two components, time paired with a    --
-- security level, on both sides of time: a box is an embargoed --
-- report or a session token, refused for being out of time or  --
-- for being tainted, and the schemes carry both components.    --
--                                                              --
-- Set 6 consists of two schemes that the report simplifies: a  --
-- var-rule disjunction entailed by another, and a product with --
-- the top absorbed. Both simplifications apply where the unit  --
-- is least; they are checked at the right-sided grades.        --
--                                                              --
-- Set 7 consists of tests of single solver stages on           --
-- hand-written constraints, each answer checked by `refl`, for --
-- steps on which the programs of the other sets do not depend, --
-- or depend only in part.                                      --
--                                                              --
-- Set 8 consists of boxes claimed after delays of rational     --
-- durations, and a box grade inferred over them, at dense      --
-- left- and right-sided time.                                  --
--                                                              --
-- Set 9 consists of programs whose conditions the solver       --
-- leaves open: the search refutes some at definitions, and the --
-- check of a run establishes, refutes or leaves unestablished  --
-- the others, at left- and right-sided time.                   --
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

-- Durations other than ticks: the generic module and its instances

import TypeInference.Examples.Durations.All

-- Solver stages on hand-written constraints

import TypeInference.Examples.Stages.All

-- Satisfiability at definitions and establishment at runs

import TypeInference.Examples.Runs.All
